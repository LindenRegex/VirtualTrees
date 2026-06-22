.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) CData.v
	$(ROCQC) ListHelpers.v
	$(ROCQC) VirtualTree.v
	$(ROCQC) Regsdata.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache
