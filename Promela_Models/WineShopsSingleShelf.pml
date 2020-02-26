#define N 2  // Shelf size
#define N2 2 // History length

// define number of instances of each process for the spins compiler
#define __instances_winery 1
#define __instances_patron 1


// Types Of Wine   //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

int wine1s;
int i = 0;
byte history[N2] = 1;
byte bw;

// A function to aid in later readability
inline updateHistory() {
	atomic {
		i = N2 - 1;
		wine1s = 0;
		do
		:: i > 0 -> 
			history[i] = history[i - 1];
			i--
		:: else -> 
			break
		od;
		history[0] = bw;
		i = N2 - 1;
		do
		:: (i >= 0) && (history[i] == 1) ->
			wine1s++;
			i--
		:: (i >= 0) && (history[i] != 1) ->
			i--
		:: else ->
			break
		od;
		i = 0;
	}
}

chan s1 = [N] of {byte}

active proctype winery() {
	// currently nondeterministic. We need it to favor s1
	do
	:: s1!1 ->
		// use the pc pointing to this next instruction
		// to label the previous action
		_ = 0
	od;
}

active proctype patron() {
	do
	:: if
	   :: s1?[bw] ->
		s1?bw;
		updateHistory()
	   fi
	od;
}
