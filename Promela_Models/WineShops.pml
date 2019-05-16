#define N 5    // Shelf size
#define N2  10 // History length

// define number of instances of each process for the spins compiler
#define __instances_winery 1
#define __instances_patron 1

//TODO Look at the 'dubious use of else' errors. They appear to behave as warnings.

// Types Of Wine   //
// 0 = No Wine     //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //

//LTL Parts (needed to make ltl checking work, not needed for buchi)
#define hasOne (wine1s >= 1)
#define hasHalfN (wine1s >= N / 2)
#define has2N (wine1s >= 2*N)

int wine1s = N2;
int i = 0; // Only use in d_step. always set to 0 at end.
byte history[N2];
byte boughtWine;

// A function to aid in later readability
inline updateHistory() {
	d_step{
		i = (2 * N) - 1;
		wine1s = 0;
		do
		:: i > 0 -> 
			history[i] = history[i - 1];
			if
			:: history[i] == 1 -> 
				wine1s++
			:: else -> 
				skip
			fi
			i--;
		:: else -> 
			break
		od;
		if
		:: boughtWine == 1 -> 
			wine1s++; 
			history[0] = 1
		:: boughtWine == 2 -> 
			history[0] = 2
		:: else -> 
			history[0] = 0
		fi
		i = 0;
	}
}



chan shelf1 = [N] of {byte}
chan shelf2 = [N] of {byte}

proctype winery(chan shipTo1, shipTo2) {
	do
	:: shipTo1 ! 1
	:: else ->
		if
		:: shipTo2 ! 2
		:: else -> skip
		fi
	od;
}

proctype patron(chan buyFrom1, buyFrom2) {
	// Wine Buying loop
	do
	:: buyFrom1 ? boughtWine -> updateHistory();
	:: else ->
		if
		:: buyFrom2 ? boughtWine -> updateHistory();
		:: else -> skip
		fi
	od;
}

init {
	// Initialize the history all in one state transition.
	d_step {
	do
	:: i < (2 * N) -> history[i] = 1; i++
	:: else -> break
	od;
	i = 0;
	}

	// Start Processes
	run winery(shelf1, shelf2);
	run patron(shelf1, shelf2);
}

// These must be commented for buchi conversion.

//# ltl alwaysOne {[] hasOne}
//# ltl eventually {<> hasOne}
//# ltl alwaysHalfN {[] hasHalfN}
//# ltl always2N {[] has2N}
