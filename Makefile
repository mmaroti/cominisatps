CXXFLAGS = -O2 -g -Wall -fmessage-length=0 -I. -Wno-unused-label -std=c++11

OBJS = core/Main.o core/Solver.o utils/Options.o utils/System.o

LIBS = -s -lz

TARGET = cominisatps

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(OBJS) $(LIBS)

all: $(TARGET)

clean:
	rm -f $(OBJS) $(TARGET)
