# Delegate commands to the src folder

.PHONY: all clean install

all:
	+make -C src $@

%:
	+make -C src $@
