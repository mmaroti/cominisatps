CXXFLAGS = -O3 -Wall -std=c++11 -D NDEBUG -I.

OBJS = core/Main.o core/Solver.o utils/Options.o utils/System.o
HEADERS = $(wildcard **/*.h)
LIBS = -s -lz

TARGET = cominisatps

%.o : %.cc $(HEADERS) Makefile
	$(CXX) -c $(CXXFLAGS) $< -o $@

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all: $(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
