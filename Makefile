GUILE ?= guile
GUILE_FLAGS = -L src

.PHONY: test check demo

test:
	$(GUILE) $(GUILE_FLAGS) tests/run-tests.scm

check: test

demo:
	$(GUILE) $(GUILE_FLAGS) src/main.scm check proofs/valid/implication.scm