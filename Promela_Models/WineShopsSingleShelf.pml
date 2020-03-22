#define N 2  // Shelf size
#define N2 2 // History length

// define number of instances of each process for the spins compiler
#define __instances_wnry 1
#define __instances_ptrn 1


// Types Of Wine   //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

int wine1s;
int i = 0;
byte h[N2] = 0;
byte bw;

// A function to aid in later readability
inline updateHistory() {
	atomic {
		i = N2 - 1;
		wine1s = 0;
		do
		:: i > 0 -> 
			h[i] = h[i - 1];
			i--
		:: else -> 
			break
		od;
		h[0] = bw;
		i = N2 - 1;
		do
		:: (i >= 0) && (h[i] == 1) ->
			wine1s++;
			i--
		:: (i >= 0) && (h[i] != 1) ->
			i--
		:: else ->
			break
		od;
		i = 0;
	}
}

chan s1 = [N] of {byte}

active proctype wnry() {
	// currently nondeterministic. We need it to favor s1
	do
	:: s1!1 ->
		// use the pc pointing to this next instruction
		// to label the previous action
		_ = 0
	od;
}

active proctype ptrn() {
	do
	:: if
	   :: s1?[bw] ->
		s1?bw;
		updateHistory()
	   fi
	od;
}
