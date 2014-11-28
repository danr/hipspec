
TARGET=$(basename $(SOURCE))_HBMC.hs
EXE=$(basename $(TARGET))
ifndef SIZE
SIZE=10
endif
HBMC_OPTS=--symbolic-size $(SIZE) --auto=False --translate-only $(HBMC_EXTRA_OPTS)

run: $(EXE)
	./$(EXE)

all: $(EXE)

clean:
	rm $(TARGET) $(EXE) -f

$(TARGET): $(SOURCE)
	hbmc $(HBMC_OPTS) $< > $@

$(EXE): $(TARGET)
	ghc --make $< -i. -i/home/dan/code/hbmc

.PHONY: run all clean
