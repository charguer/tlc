.PHONY: all clean install uninstall

all clean install uninstall:
	@ $(MAKE) -C src $@
