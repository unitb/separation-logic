
.PHONY: all clean lines

LEAN_OPT =
LEAN_PATH = $(shell pwd):/usr/local/bin/../lib/lean/library:$(shell printenv LEAN_PATH)

all:
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) --make util/ unitb/

%.olean: %.lean $(shell lean $< --deps)
	LEAN_PATH=$(LEAN_PATH) lean $(LEAN_OPT) --make $<

clean:
	/usr/bin/find . -name "*.olean" -delete

lines:
	wc `git ls-files | grep .lean`
