SOURCES=TypeCheck.hs PrettyPrint.hs LayoutToken.hs Parser.hs Syntax.hs Environment.hs Modules.hs Main.hs Equal.hs 
TESTS=Makefile Logic.pi Equality.pi Nat.pi Product.pi Fin.pi Vec.pi List.pi Lambda0.pi Lambda1.pi Lambda2.pi
SRCS=$(addprefix src/,$(SOURCES)) 

EXTRA=LICENSE README.md pi-forall.cabal stack.yaml

VERSION1=$(addprefix ../version1/,$(SRCS)) $(addprefix ../version1/test/,Lec1.pi Hw1.pi) $(EXTRA)
VERSION2=$(addprefix ../version2/,$(SRCS)) $(addprefix ../version2/test/,Lec1.pi Hw1.pi Lec2.pi Hw2.pi NatChurch.pi) $(EXTRA)
VERSION3=$(addprefix ../version3/,$(SRCS)) $(addprefix ../version3/test/,Lec1.pi Hw1.pi Lec2.pi Hw2.pi NatChurch.pi) $(EXTRA)
SOLNS=$(addprefix ../full/,$(SRCS)) $(addprefix ../full/test/, $(TESTS) Lec1.pi Hw1.pi Lec2.pi Hw2.pi Lec3.pi Fin1.pi Lec4.pi)

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg' 
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

flags=

all: version1 version2 version3 full

test : all

# BUILD = cabal new-build --disable-documentation
# EXEC = cabal new-exec pi-forall -- 

BUILD = stack build
EXEC = stack exec pi-forall --

version1: $(VERSION1)
	cd ../version1 && $(BUILD) 

test_version1: ../version1
	cd ../version1 && $(EXEC) test/Lec1.pi

version2: $(VERSION2)
	cd ../version2 && $(BUILD)

test_version2 : ../version2
	cd ../version2 && $(EXEC) test/Lec1.pi
	cd ../version2 && $(EXEC) test/Lec2.pi
	cd ../version2 && $(EXEC) test/Hw1.pi
	cd ../version2 && $(EXEC) test/Hw2.pi
	cd ../version2 && $(EXEC) test/NatChurch.pi

version3: $(VERSION3)
	cd ../version3 && $(BUILD)

full: $(SOLNS) Makefile $(EXTRA)
	cd ../full && $(BUILD)


test_full: ../full
	cd ../full/test && make


uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep pi-forall`
	@echo
	@echo You need to manually delete any pi-forall binaries on your path.
	@echo You can find them with \`which pi-forall\`

clean:
	-rm -rf src/dist src/cabal-dev ../version1/ ../version2/ ../full/ dist/ 

test:
	cd test && make

# adds a link to the executable in the test directory
pi: cabal-dev
	cabal-dev install --disable-documentation .
	ln -fs `pwd`/cabal-dev/bin/pi-forall test

# You need to have the cabal install dir on your path (by default
# ~/.cabal/bin) so that `cabal-dev` command is found.
cabal-dev:
	cabal install --overwrite-policy=always cabal-dev

../version1/% : % Makefile $(EXTRA)
	@echo ========== Creating Version 1 ==========
	@mkdir -p ../version1
	@mkdir -p ../version1/src
	@mkdir -p ../version1/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(STUBREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(STUBREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(STUBREGEX)) $@
	cp pi-forall.cabal ../version1/pi-forall.cabal
	cp LICENSE ../version1/LICENSE
	cp README.md  ../version1/README.md
	cp stack.yaml ../version1/stack.yaml


../version2/% : % Makefile $(EXTRA)
	@echo ========== Creating ../Version 2 ==========
	@mkdir -p ../version2
	@mkdir -p ../version2/src
	@mkdir -p ../version2/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(STUBREGEX)) $@
	cp pi-forall.cabal ../version2/pi-forall.cabal
	cp LICENSE ../version2/LICENSE
	cp README.md  ../version2/README.md
	cp stack.yaml ../version2/stack.yaml

../version3/% : % Makefile $(EXTRA)
	@echo ========== Creating ../Version 3 ==========
	@mkdir -p ../version3
	@mkdir -p ../version3/src
	@mkdir -p ../version3/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(STUBREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@
	cp pi-forall.cabal ../version3/pi-forall.cabal
	cp LICENSE ../version3/LICENSE
	cp README.md  ../version3/README.md
	cp stack.yaml ../version3/stack.yaml

../full/% : % Makefile $(EXTRA)
	@echo ========== Creating .hs Fulls ==========
	@mkdir -p ../full/
	@mkdir -p ../full/src
	@mkdir -p ../full/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@
	cp pi-forall.cabal ../full/pi-forall.cabal
	cp LICENSE ../full/LICENSE
	cp README.md  ../full/README.md
	cp stack.yaml ../full/stack.yaml
   # chmod 440 $@ # prevent inadvertent modification of stub code
