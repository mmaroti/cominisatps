CXXFLAGS = -O3 -Wall -std=c++11 -I. -g

OBJS = core/Main.o core/Solver.o utils/Options.o utils/System.o
HEADERS = $(wildcard **/*.h)
LIBS = -lz

TARGET = cominisatps

%.o : %.cc $(HEADERS) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all: $(TARGET)

release: CXXFLAGS += -D NDEBUG
release: LIBS += -s
release: $(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)

.PHONY: all debug clean
