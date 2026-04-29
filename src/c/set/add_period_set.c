#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <setjmp.h>
#include <unistd.h>
#include "mathematics.h"

#define TIMEOUT_RESULT (-4)

static sigjmp_buf timeout_jmp;
static volatile sig_atomic_t timeout_active = 0;

static void on_alrm(int sig)
{
    (void)sig;
    if (timeout_active)
    {
        timeout_active = 0;
        siglongjmp(timeout_jmp, 1);
    }
}

int main(int argc, const char *argv[])
{
    if (argc != 5)
    {
        fprintf(stderr,
            "Usage: %s <input.csv> <output.csv> <global|degenerate> <timeout_sec>\n"
            "  global     : pick x_max so dx-array fits and contains ~4*period gaps\n"
            "  degenerate : x_max = MAX(1000, 25 * (o_n/o_d + 1)) per row\n"
            "  timeout_sec: per-row wall-clock cap (0 disables)\n"
            "Resume: if <output.csv> already exists, the first N input data rows\n"
            "(where N = data rows in output) are skipped and processing continues.\n",
            argv[0]);
        return 1;
    }

    const char *in_path = argv[1];
    const char *out_path = argv[2];
    const char *mode = argv[3];
    const int timeout_sec = atoi(argv[4]);

    bool degenerate_mode;
    if (strcmp(mode, "global") == 0)
        degenerate_mode = false;
    else if (strcmp(mode, "degenerate") == 0)
        degenerate_mode = true;
    else
    {
        fprintf(stderr, "Unknown mode '%s'\n", mode);
        return 1;
    }

    FILE *fin = fopen(in_path, "r");
    if (!fin) { fprintf(stderr, "Error opening input '%s'\n", in_path); return 1; }

    char header[1024];
    if (!fgets(header, sizeof(header), fin))
    {
        fprintf(stderr, "Error: empty input file\n");
        fclose(fin);
        return 1;
    }
    size_t hlen = strlen(header);
    while (hlen > 0 && (header[hlen-1] == '\n' || header[hlen-1] == '\r'))
        header[--hlen] = '\0';

    // Count existing data rows in output for resume.
    size_t skip = 0;
    FILE *fout_check = fopen(out_path, "r");
    if (fout_check)
    {
        char buf[2048];
        if (fgets(buf, sizeof(buf), fout_check))
        {
            while (fgets(buf, sizeof(buf), fout_check))
                skip++;
        }
        fclose(fout_check);
    }

    FILE *fout;
    if (skip > 0)
    {
        fout = fopen(out_path, "a");
        if (!fout) { fprintf(stderr, "Error opening output '%s' for append\n", out_path); return 1; }
        printf("Resume: skipping %zu rows already in '%s'.\n", skip, out_path);
    }
    else
    {
        fout = fopen(out_path, "w");
        if (!fout) { fprintf(stderr, "Error opening output '%s'\n", out_path); return 1; }
        fprintf(fout, "%s,period_set\n", header);
    }

    // Skip already-processed input data rows.
    long long o_n, o_d, a_n, a_d, period;
    for (size_t i = 0; i < skip; i++)
    {
        if (fscanf(fin, "%lld,%lld,%lld,%lld,%lld", &o_n, &o_d, &a_n, &a_d, &period) != 5)
        {
            fprintf(stderr, "Error: input has fewer rows (%zu) than expected (%zu) for resume.\n", i, skip);
            fclose(fin); fclose(fout);
            return 1;
        }
    }

    // Install SIGALRM handler for per-row timeout.
    if (timeout_sec > 0)
    {
        struct sigaction sa;
        memset(&sa, 0, sizeof(sa));
        sa.sa_handler = on_alrm;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        if (sigaction(SIGALRM, &sa, NULL) != 0)
        {
            fprintf(stderr, "Error installing SIGALRM handler\n");
            fclose(fin); fclose(fout);
            return 1;
        }
    }

    number_t *dx = dx_alloc(MAX_PERIOD_ARRAY_SIZE);

    size_t row = skip;
    size_t failures = 0;
    size_t timeouts = 0;

    while (fscanf(fin, "%lld,%lld,%lld,%lld,%lld", &o_n, &o_d, &a_n, &a_d, &period) == 5)
    {
        row++;

        number_t x_max;
        number_t density_num = 0, density_den = 1;
        number_t target_points = 0, buffer_cap = 0;
        if (degenerate_mode)
        {
            const number_t omega_int = (number_t)(o_n / o_d) + 1;
            x_max = MAX(1000, 25 * omega_int);
        }
        else
        {
            // Cap target_points so we never request more dx slots than the
            // buffer can hold.
            density_num = ((number_t)a_n + (number_t)a_d) * (number_t)o_n;
            density_den = (number_t)a_d * (number_t)o_d;
            buffer_cap = (number_t)MAX_PERIOD_ARRAY_SIZE - 1024;
            target_points = MAX(200000, (number_t)period * 4);
            if (target_points > buffer_cap) target_points = buffer_cap;
            x_max = (target_points * density_den) / density_num;
            if (x_max > X_MAX) x_max = X_MAX;
            if (x_max < 1000) x_max = 1000;
        }

        long ps;
        if (timeout_sec > 0 && sigsetjmp(timeout_jmp, 1) != 0)
        {
            ps = TIMEOUT_RESULT;
            timeouts++;
        }
        else
        {
            if (timeout_sec > 0)
            {
                timeout_active = 1;
                alarm((unsigned)timeout_sec);
            }

            // The multiset-based estimate may not expose a full set period in
            // the trim window. On DX_LENGTH_TO_SMALL / NO_PERIOD, double x_max
            // and retry until it succeeds or the buffer / X_MAX ceiling stops
            // x_max from growing.
            while (true)
            {
                ps = lambda((number_t)a_n, (number_t)a_d,
                            (number_t)o_n, (number_t)o_d,
                            X_MIN, x_max, true, dx);

                if (degenerate_mode) break;
                if (is_legal_period_length(ps)) break;
                if (ps != DX_LENGTH_TO_SMALL && ps != NO_PERIOD) break;

                number_t new_target = target_points * 2;
                if (new_target > buffer_cap) new_target = buffer_cap;
                if (new_target <= target_points) break;

                number_t new_x_max = (new_target * density_den) / density_num;
                if (new_x_max > X_MAX) new_x_max = X_MAX;
                if (new_x_max < 1000) new_x_max = 1000;
                if (new_x_max <= x_max) break;

                target_points = new_target;
                x_max = new_x_max;
            }

            if (timeout_sec > 0)
            {
                alarm(0);
                timeout_active = 0;
            }
            if (!is_legal_period_length(ps))
                failures++;
        }

        fprintf(fout, "%lld,%lld,%lld,%lld,%lld,%ld\n",
                o_n, o_d, a_n, a_d, period, ps);
        fflush(fout);

        if (row % 100 == 0)
        {
            printf("\rRow %zu (failures: %zu, timeouts: %zu)", row, failures, timeouts);
            fflush(stdout);
        }
    }

    printf("\nDone: %zu rows total (%zu newly processed), %zu failures, %zu timeouts.\n",
           row, row - skip, failures, timeouts);

    free(dx);
    fclose(fin);
    fclose(fout);
    return 0;
}
