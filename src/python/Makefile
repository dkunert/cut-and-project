# Makefile for setting up Python environment, installing dependencies, and running the analysis

.PHONY: all venv install run clean

# Name of the Python virtual environment directory
VENV_DIR := venv

# Python interpreter to use
PYTHON := python3

# Path to the pip executable inside the virtual environment
PIP := $(VENV_DIR)/bin/pip

# Path to the python executable inside the virtual environment
PY := $(VENV_DIR)/bin/python

# List of Python packages required
REQUIREMENTS := numpy pandas scikit-learn xgboost scipy matplotlib statsmodels

all: install run

# Create a virtual environment
venv:
	$(PYTHON) -m venv $(VENV_DIR)
	@echo "Virtual environment created in $(VENV_DIR)/"

# Install required Python libraries
install: venv
	$(PIP) install --upgrade pip
	$(PIP) install $(REQUIREMENTS)
	@echo "Installed: $(REQUIREMENTS)"

# Run the main script
run:
	$(PY) main.py

# Remove virtual environment and artifacts
clean:
	rm -rf $(VENV_DIR)
	@echo "Cleaned up virtual environment"
