.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Lab07Map.v
	$(ROCQC) Lab07Language.v
	$(ROCQC) Lab07Signature.v
	$(ROCQC) Lab07Implementation.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache
