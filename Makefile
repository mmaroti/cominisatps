CXXFLAGS = -O2 -Wall -fmessage-length=0 -I. -Wno-unused-label -std=c++11

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