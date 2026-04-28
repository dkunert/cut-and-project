#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mathematics.h"

int main(int argc, const char *argv[])
{
    if (argc != 4)
    {
        fprintf(stderr,
            "Usage: %s <input.csv> <output.csv> <global|degenerate>\n"
            "  global     : x_max = X_MAX (=%d) for every row\n"
            "  degenerate : x_max = MAX(1000, 25 * (o_n/o_d + 1)) per row\n",
            argv[0], X_MAX);
        return 1;
    }

    const char *in_path = argv[1];
    const char *out_path = argv[2];
    const char *mode = argv[3];

    bool degenerate_mode;
    if (strcmp(mode, "global") == 0)
        degenerate_mode = false;
    else if (strcmp(mode, "degenerate") == 0)
        degenerate_mode = true;
    else
    {
        fprintf(stderr, "Unknown mode '%s'. Expected 'global' or 'degenerate'.\n", mode);
        return 1;
    }

    FILE *fin = fopen(in_path, "r");
    if (!fin) { fprintf(stderr, "Error opening input '%s'\n", in_path); return 1; }
    FILE *fout = fopen(out_path, "w");
    if (!fout) { fprintf(stderr, "Error opening output '%s'\n", out_path); fclose(fin); return 1; }

    char header[1024];
    if (!fgets(header, sizeof(header), fin))
    {
        fprintf(stderr, "Error: empty input file\n");
        fclose(fin); fclose(fout);
        return 1;
    }
    size_t hlen = strlen(header);
    while (hlen > 0 && (header[hlen-1] == '\n' || header[hlen-1] == '\r'))
        header[--hlen] = '\0';
    fprintf(fout, "%s,period_set\n", header);

    number_t *dx = dx_alloc(MAX_PERIOD_ARRAY_SIZE);

    long long o_n, o_d, a_n, a_d, period;
    size_t row = 0;
    size_t failures = 0;

    while (fscanf(fin, "%lld,%lld,%lld,%lld,%lld", &o_n, &o_d, &a_n, &a_d, &period) == 5)
    {
        row++;

        number_t x_max;
        if (degenerate_mode)
        {
            const number_t omega_int = (number_t)(o_n / o_d) + 1;
            x_max = MAX(1000, 25 * omega_int);
        }
        else
        {
            x_max = X_MAX;
        }

        const long ps = lambda((number_t)a_n, (number_t)a_d,
                               (number_t)o_n, (number_t)o_d,
                               X_MIN, x_max, true, dx);
        if (!is_legal_period_length(ps))
            failures++;

        fprintf(fout, "%lld,%lld,%lld,%lld,%lld,%ld\n",
                o_n, o_d, a_n, a_d, period, ps);

        if (row % 100 == 0)
        {
            printf("\rRow %zu (failures: %zu)", row, failures);
            fflush(stdout);
        }
    }

    printf("\nDone: %zu rows processed, %zu lambda failures.\n", row, failures);

    free(dx);
    fclose(fin);
    fclose(fout);
    return 0;
}
