/* Broadcast Algorithm description */

int nsnt;

proctype FaultyProc() {
	int i = 0;
	step: atomic {
		do
			:: i < 4 -> nsnt++; i = 4;
			:: i < 4 -> i++;
			:: i == 4 -> break;
		od
	};
}

proctype CorrectProc() {
	byte status, nstatus;
	int rcvd = 0;
	int nrcvd = 0;
	if
		:: status = 0;
		:: status = 1;
	fi;
	step: atomic {
		if
			:: (nrcvd < nsnt + 1) -> nrcvd = rcvd + 1;
			:: else: nrcvd = rcvd;
		fi;
		rcvd = nrcvd;
		if
			:: (rcvd >= 3) ->
				nstatus = 3;
			:: (status == 1 || rcvd >= 2) -> nstatus = 2;
			:: else -> nstatus = status;
		fi;
		if
			:: (status == 0 || status == 1) && (nstatus == 2 || nstatus == 3) -> nsnt++;
			:: else;
		fi;
		status = nstatus;
		nstatus = 255;
	} goto step;
}



/* init system here */
init {
	atomic {
		run CorrectProc();
		run CorrectProc();
		run CorrectProc();
		run FaultyProc();
	}
}



/* LTL formulas to check */
ltl unforgeability { [](((CorrectProc[0]@step && CorrectProc[1]@step && CorrectProc[2]@step) && (CorrectProc[0]:status == 0 && CorrectProc[1]:status == 0 && CorrectProc[2]:status == 0)) -> <>(CorrectProc[0]:status != 3 && CorrectProc[1]:status != 3 && CorrectProc[2]:status != 3)) }

ltl correctness { [](((CorrectProc[0]@step && CorrectProc[1]@step && CorrectProc[2]@step) && (CorrectProc[0]:status == 1 && CorrectProc[1]:status == 1 && CorrectProc[2]:status == 1)) -> <>(CorrectProc[0]:status == 3 || CorrectProc[1]:status == 3 || CorrectProc[2]:status == 3)) }

ltl relay { []((CorrectProc[0]:status == 3 || CorrectProc[1]:status == 3 || CorrectProc[2]:status == 3) -> <>(CorrectProc[0]:status == 3 && CorrectProc[1]:status == 3 && CorrectProc[2]:status == 3)) }
