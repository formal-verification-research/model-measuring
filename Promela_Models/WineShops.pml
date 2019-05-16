#define N 5
#define N2  10

//LTL Parts
#define hasOne (wine1s >= 1)
#define hasHalfN (wine1s >= N / 2)
#define has2N (wine1s >= 2*N)

int wine1s = 2 * N;
int i = 0; // Only use in d_step. always set to 0 at end.
byte history[N2];

byte boughtWine;

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

// used whenever a wine is received by the patron

// Types Of Wine   //
// 0 = No Wine     //
// 1 = Shop 1 Wine //
// 2 = Show 2 Wine //


chan shelf1     = [N] of {byte}
chan shelf2     = [N] of {byte}

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
	d_step {/*{{{*/
	do
	:: i < (2 * N) -> history[i] = 1; i++
	:: else -> break
	od;
	i = 0;
	}/*}}}*/

	run winery(shelf1, shelf2);
	run patron(shelf1, shelf2);
}


//# ltl alwaysOne {[] hasOne}
//# ltl eventually {<> hasOne}
//# ltl alwaysHalfN {[] hasHalfN}
//# ltl always2N {[] has2N}
