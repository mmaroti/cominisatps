CXXFLAGS = -O3 -Wall -Wno-unused-label -std=c++11 -I.

OBJS = core/Main.o core/Solver.o utils/Options.o utils/System.o
HEADERS = $(wildcard **/*.h)
LIBS = -s -lz

TARGET = cominisatps

%.o : %.cc $(HEADERS)
	$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) $< -o $@

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all: $(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
