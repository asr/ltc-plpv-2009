publish = $(shell if [ -e publish.mk ]; then echo Yes; else echo No; fi)
ifeq ($(publish),Yes)
include publish.mk
endif

AGDA = agda -isrc

tarball_name = ltc-plpv-2009.tar.gz

test :
	$(AGDA) src/LTC.agda

test_without_interfaces :
	$(AGDA) --ignore-interfaces src/LTC.agda

publish_html :
	rm -r -f html/
	$(AGDA) --html src/LTC.agda
	$(RSYNC) html $(host_dir)

publish_tarball :
	darcs dist
	$(RSYNC) $(tarball_name) $(host_dir)

clean :
	find -name '*.agdai' | xargs rm -f
	rm -r -f html/
	rm -f $(tarball_name)
