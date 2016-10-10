.PHONY: all install uninstall

all install uninstall:
	@ $(MAKE) -C src $@
