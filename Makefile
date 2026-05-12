.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Lab07Map.v
	$(ROCQC) Lab07Language.v
	$(ROCQC) GDS_Language.v
	$(ROCQC) GDS_Testing.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache
