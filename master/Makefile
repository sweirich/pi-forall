SOURCES=TypeCheck.hs PrettyPrint.hs LayoutToken.hs Parser.hs Syntax.hs Environment.hs Modules.hs Main.hs Equal.hs 
TESTS=Makefile Equality.pi Nat.pi Product.pi Fin.pi Vec.pi 
SRCS=$(addprefix src/,$(SOURCES)) 

EXTRA=LICENSE README pi-forall.cabal

VERSION1=$(addprefix ../version1/,$(SRCS)) $(addprefix ../version1/test/,Lec1.pi Hw1.pi)
VERSION2=$(addprefix ../version2/,$(SRCS)) $(addprefix ../version2/test/,Lec1.pi Hw1.pi Lec2.pi Hw2.pi)
VERSION3=$(addprefix ../version3/,$(SRCS)) $(addprefix ../version3/test/,Lec1.pi Hw1.pi Lec2.pi Hw2.pi Nat.pi Fin1.pi Product1.pi)
SOLNS=$(addprefix ../soln/,$(SRCS)) $(addprefix ../soln/test/, $(TESTS))

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg' 
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

all: version1 version2 version3 soln

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

version3: $(VERSION3)
	cd ../version3 &&	cabal install --disable-documentation . 

test_version3: ../version3
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Lec1.pi
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Lec2.pi
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Hw1.pi
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Hw2.pi
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Nat.pi
	../version3/dist/build/pi-forall/pi-forall ../version3/test/Fin1.pi

soln: $(SOLNS) Makefile
	cd ../soln && cabal install --disable-documentation . 

test_soln: ../soln
	cd ../soln/test && make


uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep pi-forall`
	@echo
	@echo You need to manually delete any trellys binaries on your path.
	@echo You can find them with \`which pi-forall\`

clean:
	-rm -rf src/dist src/cabal-dev ../version1/ ../version2/ ../version3/ soln/ dist/ 

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
	cp README  ../version1/README


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
	cp README  ../version2/README


../version3/% : % Makefile
	@echo ========== Creating ../Version 3 ==========
	@mkdir -p ../version3
	@mkdir -p ../version3/src
	@mkdir -p ../version3/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(STUBREGEX)) $@
	cp pi-forall.cabal ../version3/pi-forall.cabal
	cp LICENSE ../version3/LICENSE
	cp README  ../version3/README


../soln/% : % Makefile
	@echo ========== Creating .hs Solns ==========
	@mkdir -p ../soln/
	@mkdir -p ../soln/src
	@mkdir -p ../soln/test
	-chmod 640 $@
	cp $< $@
	perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN DATA,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@
	cp pi-forall.cabal ../soln/pi-forall.cabal
	cp LICENSE ../soln/LICENSE
	cp README  ../soln/README


   # chmod 440 $@ # prevent inadvertent modification of stub code