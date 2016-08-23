SOURCES=TypeCheck.hs PrettyPrint.hs LayoutToken.hs Parser.hs Syntax.hs Environment.hs Modules.hs Main.hs Equal.hs 
TESTS=Makefile Logic.pi Equality.pi Nat.pi Product.pi Fin.pi Vec.pi List.pi Lambda0.pi Lambda1.pi Lambda2.pi
SRCS=$(addprefix src/,$(SOURCES)) 

EXTRA=LICENSE README.md pi-forall.cabal Setup.hs

VERSION1=$(addprefix ../version1/,$(SRCS)) $(addprefix ../version1/test/,Lec1.pi Hw1.pi)
VERSION2=$(addprefix ../version2/,$(SRCS)) $(addprefix ../version2/test/,Lec1.pi Hw1.pi Lec2.pi Hw2.pi NatChurch.pi)
SOLNS=$(addprefix ../full/,$(SRCS)) $(addprefix ../full/test/, $(TESTS) Lec1.pi Hw1.pi Lec2.pi Hw2.pi Lec3.pi Fin1.pi Lec4.pi)

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg' 
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

flags=

all: version1 version2 full

test : all


version1: $(VERSION1)
	cd ../version1 && cabal install --disable-documentation . 

test_version1: ../version1
	../version1/dist/build/pi-forall/pi-forall ../version1/test/Lec1.pi

version2: $(VERSION2)
	cd ../version2 && cabal install --disable-documentation . 

test_version2 : ../version2
	../version2/dist/build/pi-forall/pi-forall ../version2/test/Lec1.pi
	../version2/dist/build/pi-forall/pi-forall ../version2/test/Lec2.pi
	../version2/dist/build/pi-forall/pi-forall ../version2/test/Hw1.pi
	../version2/dist/build/pi-forall/pi-forall ../version2/test/Hw2.pi
	../version2/dist/build/pi-forall/pi-forall ../version2/test/NatChurch.pi

# full: $(SOLNS) Makefile
# 	cd ../full && cabal install --disable-documentation . 

# --force-reinstalls needed only on debian testing / ghc 7.8.4
full: $(SOLNS) Makefile
	cd ../full && cabal install --disable-documentation $(flags) . 


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
	cabal install cabal-dev

../version1/% : % Makefile
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
	cp Setup.hs ../version1/Setup.hs


../version2/% : % Makefile
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
	cp Setup.hs ../version1/Setup.hs

../full/% : % Makefile
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
	cp Setup.hs ../version1/Setup.hs

   # chmod 440 $@ # prevent inadvertent modification of stub code
