.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) CData.v
	$(ROCQC) VirtualTree.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache
