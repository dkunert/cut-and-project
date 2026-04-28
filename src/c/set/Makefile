# ==================
# 1. Basic variables
# ==================
CC        ?= gcc
OS         := $(shell uname -s)
ARCH       := $(shell uname -m)
EXE        :=
STD_FLAGS  := -std=c11 -MMD

# =====================================
# 2. Platform-specific flags & compiler
# =====================================
ifeq ($(OS),Darwin)
  # macOS: use clang
  CC              := clang
  ifeq ($(ARCH),arm64)
    PERF_ARCH_FLAGS := -march=armv8.6-a+fp16 -mtune=apple-m2
  else
    PERF_ARCH_FLAGS := -march=native -mtune=native
  endif
  DEBUG_ARCH_FLAGS :=
else ifeq ($(OS),Linux)
  # Linux: use default architecture tuning
  PERF_ARCH_FLAGS := -march=native -mtune=native
  DEBUG_ARCH_FLAGS :=
else ifeq ($(OS),Windows_NT)
  # Windows under MSYS2/MinGW: use MinGW GCC and add .exe suffix
  EXE             := .exe
  CC              := x86_64-w64-mingw32-gcc
  PERF_ARCH_FLAGS := -march=x86-64
  DEBUG_ARCH_FLAGS :=
endif

# ==============================
# 3. Performance and debug flags
# ==============================
CFLAGS_PERF  := -O3 $(PERF_ARCH_FLAGS) -flto -funroll-loops -ffast-math -fno-finite-math-only $(STD_FLAGS)
CFLAGS_DEBUG := -O0 -g $(DEBUG_ARCH_FLAGS) $(STD_FLAGS)

# ====================
# 4. Sources & targets
# ====================
SOURCES       := main.c mathematics.c test.c conjectures.c
OBJS_PERF     := $(SOURCES:.c=.perf.o)
OBJS_DEBUG    := $(SOURCES:.c=.debug.o)
DEPS          := $(OBJS_PERF:.perf.o=.d) $(OBJS_DEBUG:.debug.o=.d)
TARGET_PERF   := cnp$(EXE)
TARGET_DEBUG  := cnp_debug$(EXE)

.PHONY: all perf debug clean
all: perf debug

# -----------------
# Performance build
# -----------------
perf: $(TARGET_PERF)

$(TARGET_PERF): $(OBJS_PERF)
	$(CC) $(CFLAGS_PERF) -o $@ $^

# -----------
# Debug build
# -----------
debug: $(TARGET_DEBUG)

$(TARGET_DEBUG): $(OBJS_DEBUG)
	$(CC) $(CFLAGS_DEBUG) -o $@ $^

# ==========================
# 5. Pattern rules & cleanup
# ==========================
%.perf.o: %.c
	$(CC) $(CFLAGS_PERF) -c $< -o $@

%.debug.o: %.c
	$(CC) $(CFLAGS_DEBUG) -c $< -o $@

-include $(DEPS)

clean:
	rm -f $(OBJS_PERF) $(OBJS_DEBUG) $(DEPS) $(TARGET_PERF) $(TARGET_DEBUG)
