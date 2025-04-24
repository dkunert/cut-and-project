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

Please configure ```constants.h```, especially ```MAX_PERIOD_ARRAY_SIZE``` before running it!

##### constants.h

```c
#ifndef CONSTANTS_H
#define CONSTANTS_H

#define MAX_PERIOD_ARRAY_SIZE 8000000000
#define X_MIN 0
#define X_MAX 1000000
#define NUMBER_OF_TESTS 1000
#define MAX_RANDOM 100000
#define MAX_NOMINATOR_DENOMINATOR 100000
#define TASKS TEST | TEST_CONJECTURES
#define CREATE_FILE_TO_FIND_A_PATTERN false
#define NUMBER_OF_LINES_IN_THE_PATTERN_FILE 100000

#define NO_PERIOD -1
#define ARRAY_SIZE_EXCEEDED -2
#define DX_LENGTH_TO_SMALL -3
#define FRACTION_OF_REMAINING_ELEMENTS 0.9

#define TEST_FILE "./pattern_x_max_1000000_1000_lines.csv"
#define FILE_TO_FIND_PATTERN "./find_pattern_x_max_1000000_%d_lines.csv"

#endif /* CONSTANTS_H */
```

| Definition                                | Comment                                                                                  |
|-------------------------------------------|------------------------------------------------------------------------------------------|
| ```MAX_PERIOD_ARRAY_SIZE```               | Please adjust this. With a size of 8,000,000,000 about 60 GB of RAM is used!             |
| ```X_MIN```                               | x interval starts here. ```X_MIN``` is included.                                         |
| ```X_MAX```                               | x interval ends here. ```X_MAX``` is included.                                           |
| ```NUMBER_OF_TESTS```                     | number of tests **FOR WHAT?**                                                            |
| ```MAX_RANDOM```                          | maximum for random numbers                                                               |
| ```MAX_NOMINATOR_DENOMINATOR```           | maximum number for the dominator for random rationals                                    |
| ```TASKS```                               | Tests and/or tests conconjectures can be performed.                                      |
| ```CREATE_FILE_TO_FIND_A_PATTERN```       | When tests are done, you can create a file to check the patterns as well.                |
| ```NUMBER_OF_LINES_IN_THE_PATTERN_FILE``` | This pattern file will have NUMBER_OF_LINES_IN_THE_PATTERN_FILE lines (plus a headline). |

#### Makefile

The makefile supports macOS, Linux and Windows.

There are three targets:

* ```make debug``` creates debug code.
* ```make perf``` produces performance code.
* ```make all``` produces performance and debug code.
* ```make clean``` cleans up.

You can excecute the performance code with ```./cnp``` and the debug code with ```./cnp_debug```.

#### Python Code

There are four targets:

* ```make install``` installs all required libraries.
* ```make run``` runs the software.
* ```make all``` installs all required libraries and runs the software.
* ```make clean``` cleans up.
