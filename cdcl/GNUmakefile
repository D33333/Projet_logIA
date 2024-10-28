include GNUmakefile.conf

#################
#   General     #
#################

.PHONY: default
default: build

.PHONY: all
all: build

.PHONY: build
build:
	dune build --profile release

cdcl: build
	ln -s _build/install/default/bin/cdcl cdcl || true

.PHONY: doc
doc:
	dune build @doc

.PHONY: clean
clean:
	dune clean
	@rm -rf $(FIRSTNAME)_$(LASTNAME).tar.gz

TIMEOUT=30
SUDOKUSTART=0
NSUDOKU=10

#################
#      CDCL     #
#################


.PHONY: tests
tests: build cdcl
	./tests/run.sh $(TIMEOUT)

.PHONY: tests_new
tests_new: build cdcl
	./tests/run_new.sh $(TIMEOUT)

#################
#     Sudoku    #
#################

.PHONY: sudoku
sudoku: build cdcl
	./sudoku/run.sh $(TIMEOUT) $(SUDOKUSTART) $(NSUDOKU)
