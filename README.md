# cut-and-project

## Conjectures on the Period Lengths of One-Dimensional Cut-and-Project Sequences

With $\alpha, \beta \in ℕ$, $\alpha \perp \beta$, $x, y \in ℝ$, $\omega \in \mathbb{R}_{\ge 0}$ and $i \in ℤ$, we consider the points

$$
P =
\biggl(
(x, y)
\Bigm|
x \in ℤ,
y \in
\bigl[\tfrac{\alpha}{\beta}(x-\omega), \tfrac{\alpha}{\beta}x+\omega\bigr]
\cap ℤ
\biggr)
$$

projected vertically onto

$$
f(x) = \frac{\alpha}{\beta}x
$$

and measure their Euclidean distances $(d^{(i)})$.

With

$$
\Lambda_{\alpha,\beta} := \alpha + \beta + 1,
$$

we propose the following conjectures concerning the period length $\lambda$ of $(d^{(i)})$:

1. There is always a finite $\lambda$.
2. If $\omega \in (0,1)$, then $\lambda_{\alpha,\beta} < \Lambda_{\alpha,\beta}$.
3. If $\omega = 1$, then $\lambda_{\alpha,\beta} = \Lambda_{\alpha,\beta}$.
4. If $\omega \in (1,2)$, then $\lambda_{\alpha,\beta} \ge \Lambda_{\alpha,\beta}$.
5. If $\omega > 2$, then $\lambda_{\alpha,\beta} > \Lambda_{\alpha,\beta}$.
6. If $\omega \ne 1$, then $\displaystyle \lambda \approx \bigl\lfloor \omega \,\Lambda_{\alpha,\beta}\bigr\rfloor$.

We use numerical methods to support these conjectures.

We will show that $\lambda_{\omega=0} = 1$. Conjecture 6 is the result of a conversation with [ChatGPT's](https://chat.openai.com) model _o3-mini-high_.

## Content

### LaTeX Code and PDF

Please find the LaTeX Code and the PDF in directory ```LaTeX```.

### Sorces

Please find the C and the Python code in direcory ```src```. The sub-directories for C and Python contain makefiles.
I have used _ChatGPT_ for both codebases.

#### C Code

#### Configuration

Please configure the code before running it!

##### constants.h

```c
#ifndef CONSTANTS_H
#define CONSTANTS_H

#define MAX_PERIOD_ARRAY_SIZE 8000000000
#define X_MIN 0
#define X_MAX 1000000
#define NUMBER_OF_TESTS 1000
#define MAX_NOMINATOR_DENOMINATOR 100000

#define NO_PERIOD -1
#define ARRAY_SIZE_EXCEEDED -2
#define DX_LENGTH_TO_SMALL -3
#define FRACTION_OF_REMAINING_ELEMENTS 0.9
#define MAX_RANDOM 100000

#define TEST_FILE "./pattern_x_max_1000000_1000_lines.csv"
#define FILE_TO_FIND_PATTERN "./find_pattern_x_max_1000000_%d_lines.csv"

#endif /* CONSTANTS_H */
```

Please adjust ```MAX_PERIOD_ARRAY_SIZE```. With a size of 8,000,000,000 about 60 GB of RAM is used!

#### Makefile

The makefile supports macOS, Linux and Windows.

There are three targets:

* ```make debug``` creates debug code.
* ```make perf``` produces performance code.
* ```make all``` produces performance and debug code.
* ```make clean``` cleans up.

You can excecute the performance code with ```./cnp``` and the debug code with ```./cnp_debug```.

#### main.c

```c
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "test.h"
#include "conjectures.h"

int main(int argc, const char *argv[])
{
    number_t *dx = dx_alloc(MAX_PERIOD_ARRAY_SIZE);

    enum Tasks
    {
        TEST = 1 << 0,             // 0b00000001
        TEST_CONJECTURES = 1 << 1, // 0b00000010
    };

    uint8_t tasks = TEST | TEST_CONJECTURES;

    if (tasks & TEST) {
        const bool create_file_to_find_a_pattern = false;
        test(create_file_to_find_a_pattern, dx);
    }
    if (tasks & TEST_CONJECTURES)
        test_conjectures(dx);

    free(dx);
    return 0;
}
```

By setting ```tasks```, you can configure the tasks. By ```setting create_file_to_find_a_pattern```, you can decide of a file to find a pattern is created.

#### tests.c




#### Python Code

There are four targets:

* ```make install``` installs all required libraries.
* ```make run``` runs the software.
* ```make all``` installs all required libraries and runs the software.
* ```make clean``` cleans up.
