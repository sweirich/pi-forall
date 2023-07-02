SOURCES=TypeCheck.hs PrettyPrint.hs LayoutToken.hs Parser.hs Syntax.hs Environment.hs Modules.hs Arbitrary.hs Equal.hs 
TEST_VERSION1 = Lec1.pi 
TEST_VERSION2 = $(TEST_VERSION1) Lec2.pi Hw1.pi Hw2.pi NatChurch.pi Sigma.pi
TEST_VERSION3 = $(TEST_VERSION2) Lec3.pi
TEST_FULL=Makefile $(TEST_VERSION3) Logic.pi Equality.pi Product.pi Nat.pi Fin.pi FinHw.pi Vec.pi BoolLib.pi List.pi Lambda.pi Lambda0.pi Lambda1.pi Lambda2.pi BoolLib.pi Lec4.pi Product1.pi Fix.pi Lennart.pi Hurkens.pi Equal.pi
SRCS=$(addprefix src/,$(SOURCES)) app/Main.hs test/Main.hs

EXTRA=LICENSE README.md pi-forall.cabal stack.yaml 

VERSION1=$(addprefix ../version1/,$(SRCS)) $(addprefix ../version1/pi/,$(TEST_VERSION1)) ../version1/pi/Hw1.pi $(EXTRA)
VERSION2=$(addprefix ../version2/,$(SRCS)) $(addprefix ../version2/pi/,$(TEST_VERSION2)) $(EXTRA)
VERSION3=$(addprefix ../version3/,$(SRCS)) $(addprefix ../version3/pi/,$(TEST_VERSION3)) $(EXTRA)
SOLNS=$(addprefix ../full/,$(SRCS)) $(addprefix ../full/pi/, $(TEST_FULL)) 

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg' 
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

FORMAT=ormolu --ghc-opt -XImportQualifiedPost --mode inplace

flags=

all: version1 version2 version3 full

test : all test_version1 test_version2 test_version3 test_full

# BUILD = cabal new-build --disable-documentation
# EXEC = cabal new-exec pi-forall -- 

BUILD = stack build
EXEC = stack exec pi-forall --

version1: $(VERSION1)
	cd ../version1 && $(BUILD) 

test_version1: ../version1
	@for FILE in $(TEST_VERSION1); do cd ../version1 && $(EXEC) pi/$$FILE ; done
	stack test

version2: $(VERSION2)
	cd ../version2 && $(BUILD)

test_version2 : ../version2
	@for FILE in $(TEST_VERSION2); do cd ../version2 && $(EXEC) pi/$$FILE ; done
	stack test

version3: $(VERSION3)
	cd ../version3 && $(BUILD)

test_version3 : ../version3
	@for FILE in $(TEST_VERSION3); do cd ../version3 && $(EXEC) pi/$$FILE ; done
	stack test

full: $(SOLNS) Makefile $(EXTRA)
	cd ../full && $(BUILD)


test_full: ../full
	cd ../full/pi && make
	stack test


uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep pi-forall`
	@echo
	@echo You need to manually delete any pi-forall binaries on your path.
	@echo You can find them with \`which pi-forall\`

clean:
	-rm -rf ../version1/ ../version2/ ../full/ dist/ dist-newstyle/ .stack-work/

test:
	cd pi && make

# adds a link to the executable in the test directory
pi: cabal-dev
	cabal-dev install --disable-documentation .
	ln -fs `pwd`/cabal-dev/bin/pi-forall pi

# You need to have the cabal install dir on your path (by default
# ~/.cabal/bin) so that `cabal-dev` command is found.
cabal-dev:
	cabal install --overwrite-policy=always cabal-dev

../version1 : Makefile $(EXTRA)
	@echo ========== Creating Version 1 ==========
	@mkdir -p ../version1
	@mkdir -p ../version1/src
	@mkdir -p ../version1/pi
	@mkdir -p ../version1/app
	@mkdir -p ../version1/test
	cp pi-forall.cabal ../version1/pi-forall.cabal
	cp LICENSE ../version1/LICENSE
	cp README.md  ../version1/README.md
	cp stack.yaml ../version1/stack.yaml

../version1/% : % Makefile $(EXTRA) ../version1
#	-chmod 640 $@ 2> /dev/null
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN HW,$(STUBREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EQUAL,$(STUBREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EP,$(STUBREGEX)) $@
	@if [[ $@ == *.hs ]]; then $(FORMAT) $@; fi

../version2 : Makefile $(EXTRA)
	@echo ========== Creating ../Version 2 ==========
	@mkdir -p ../version2
	@mkdir -p ../version2/src
	@mkdir -p ../version2/pi
	@mkdir -p ../version2/app
	@mkdir -p ../version2/test
	cp pi-forall.cabal ../version2/pi-forall.cabal
	cp LICENSE ../version2/LICENSE
	cp README.md  ../version2/README.md
	cp stack.yaml ../version2/stack.yaml

../version2/% : % Makefile $(EXTRA) ../version2
#	-chmod 640 $@ 2> /dev/null
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EP,$(STUBREGEX)) $@

../version3 : Makefile $(EXTRA) 
	@echo ========== Creating ../Version 3 ==========
	@mkdir -p ../version3
	@mkdir -p ../version3/src
	@mkdir -p ../version3/pi
	@mkdir -p ../version3/app
	@mkdir -p ../version3/test
	cp pi-forall.cabal ../version3/pi-forall.cabal
	cp LICENSE ../version3/LICENSE
	cp README.md  ../version3/README.md
	cp stack.yaml ../version3/stack.yaml

../version3/% : % Makefile $(EXTRA) ../version3
#	-chmod 640 $@ 2> /dev/null
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@

../full : Makefile $(EXTRA)
	@echo ========== Creating .hs Fulls ==========
	@mkdir -p ../full/
	@mkdir -p ../full/src
	@mkdir -p ../full/pi
	@mkdir -p ../full/app
	@mkdir -p ../full/test
	cp pi-forall.cabal ../full/pi-forall.cabal
	cp LICENSE ../full/LICENSE
	cp README.md  ../full/README.md
	cp stack.yaml ../full/stack.yaml

../full/% : % Makefile $(EXTRA) ../full
#	-chmod 640 $@ 2> /dev/null
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN DATA,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@
#	chmod 440 $@ # prevent inadvertent modification of stub code
