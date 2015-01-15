
TARGET=$(basename $(SOURCE))_HBMC.hs
EXE=$(basename $(TARGET))
HBMC_OPTS=--auto=False --translate-only $(HBMC_EXTRA_OPTS)

run: $(EXE)
	./$(EXE)

all: $(EXE)

clean:
	rm $(TARGET) $(EXE) -f

$(TARGET): $(SOURCE)
	hbmc $(HBMC_OPTS) $< > $@

$(EXE): $(TARGET)
	ghc -O2 --make $< -i. -i/home/dan/code/hbmc

.PHONY: run all clean
