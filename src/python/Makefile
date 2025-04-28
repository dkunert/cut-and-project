.PHONY: all venv install run clean

VENV_DIR := venv
PYTHON   := python3
PY       := $(VENV_DIR)/bin/python
PIP      := $(PY) -m pip

REQUIREMENTS := numpy pandas scikit-learn xgboost scipy matplotlib statsmodels

all: install run

# Create a virtual environment (and upgrade pip/setuptools/wheel on Python ≥3.9)
venv:
	$(PYTHON) -m venv --upgrade-deps $(VENV_DIR)
	@echo "Virtual environment created in $(VENV_DIR)/"

install: venv
	$(PIP) install --upgrade pip
	$(PIP) install $(REQUIREMENTS)
	@echo "Installed: $(REQUIREMENTS)"

run:
	$(PY) main.py

clean:
	rm -rf $(VENV_DIR)
	@echo "Cleaned up virtual environment"