# Main Rules
# ==========
#
# make [all]: does a regression test, by checking that everything that
#             was correctly passing (failing) type checking is still
#             passing (failing) type checking.
#
# make todo: tests if known-broken things are still broken.  If you
#            fix something in TODO_PASS (TODO_FAIL) then you should
#            move it to PASS (FAIL).

# Use bash to run targets.
SHELL=/bin/bash

# PASS are tests that *should* always pass.
PASS=Logic Equality Product Nat Fin Vec BoolLib Hw1 Hw2 FinHw \
    Lambda Lambda0 Lambda1 Lambda2 \
	Lec1 Lec2 Lec3 Lec4 \
	List NatChurch Product1 Lennart Hurkens
 
# TODO_FAIL are tests that *should* fail but currently pass.
TODO_FAIL=
# TODO_PASS are tests that *should* pass but currently fail.
TODO_PASS=
# stale?
UNKNOWN=
# A symlink to the local pi-forall, installed by top level make.
PI=pi-forall
# typecheck *quietly*
TYPECHECK=stack exec pi-forall 1>/dev/null # 2>&1

.PHONY: pass fail todo_pass todo_fail todo

all: pass fail

clean:
	rm *.pi-elaborated

pass: $(foreach p,$(PASS),$(p).pass)

fail:


todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
todo_fail: $(foreach f,$(TODO_FAIL),$(f).fail)
todo: todo_pass
	@echo
	@echo "Any names printed *without* errors should be moved from TODO_* to *"

%.pass:	%.pi
	@echo -n "$<: "
	@if ! $(TYPECHECK) $<; then echo -e "\033[1;31mfailed\033[0;30m (should pass)" >&2; else echo; fi

%.fail: %.pi
	@echo -n "$<: "
	@if $(TYPECHECK) $<; then echo -e "\033[1;31mpassed\033[0;30m (should fail)" >&2; else echo; fi
