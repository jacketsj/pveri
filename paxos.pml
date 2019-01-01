/* Paxos description */

chan proposal = [20] of {int,int};
chan promise = [20] of {int,int,int};
chan accept = [20] of {int,int,int};
chan learn = [20] of {int,int,int};
int learnerId, learnerRound, learnerVal;
int lastLearnVal = -1;
int mcount[20];


inline receive_promise(round, count, newRound, newVal, currRound, currVal) {
	d_step {
		promise??eval(round), newRound, newVal ->
			if :: count < 2 -> count++;
			   :: else
			fi;
			if :: newRound > currRound ->
				currRound = newRound;
				currVal = newVal;
			   :: else
			fi;
	}
}


inline send_accept(round, count, currRound, currVal, tempVal, tempRound) {
	d_step {
		count >= 2 ->
			if :: currVal < 0 -> tempRound = round; tempVal = myVal; 
			   :: else -> tempRound = currRound; tempVal = currVal;
			fi;
	}
	for(i:1..3) {
		accept!i,tempRound,tempVal;
	}
	break;
}


inline receive_proposal(id, proposedRound, round, acceptercurrVal) {
	atomic {
		proposal??eval(id),proposedRound ->
			if :: (proposedRound > round) ->
				promise!proposedRound,round,acceptercurrVal;
				round = proposedRound;
			fi;
	}
}


inline receive_accept(id, acceptRound, acceptVal, round, acceptercurrVal) {
	atomic {
		accept??eval(id),acceptRound,acceptVal ->
			if :: (acceptRound >= round) ->
				round = acceptRound;
				acceptercurrVal = acceptVal;
				learn!id,round,acceptercurrVal;
			fi;
	}
}



proctype proposer(int proposerRound, myVal) {
	int count = 0;
	int currRound = -1;
	int proposerCurrVal = -1;
	int newRound, newVal;
	int i;
	int tempVal, tempRound;

	for(i:1..3) {
		proposal!i,proposerRound;
	}
S1:	do
		:: receive_promise(proposerRound, count, newRound, newVal, currRound, proposerCurrVal);
		:: send_accept(proposerRound, count, currRound, proposerCurrVal, tempVal, tempRound);
		//:: timeout -> goto S1;
	od
}



proctype accepter(int id) {
	int proposedRound, acceptRound, acceptVal;

	int round = -1;
	int acceptercurrVal = -1;

S2:	do		
		:: receive_proposal(id, proposedRound, round, acceptercurrVal);
		:: receive_accept(id, acceptRound, acceptVal, round, acceptercurrVal);
		:: timeout -> goto S2;
	od
}



proctype learner() {

S3:	do
		:: d_step {
			learn??learnerId,learnerRound,learnerVal ->
			if :: mcount[learnerRound] < 2 -> mcount[learnerRound]++;
			   :: else
			fi;
			if :: mcount[learnerRound] >= 2 -> printf("Learner learned (round: %d, value: %d\n)", learnerRound, learnerVal);
				if :: (lastLearnVal > -1 && lastLearnVal != learnerVal) ->
					assert(lastLearnVal == learnerVal);
				   :: else lastLearnVal = learnerVal;
				fi;
			   :: else
			fi;
		   }
		//:: timeout -> goto S3;
	od
}



/* init system here */
init {
	atomic {
		run proposer(1, 1);
		run proposer(2, 2);
		run accepter(1);
		run accepter(2);
		run accepter(3);
		run learner();
	}
}
