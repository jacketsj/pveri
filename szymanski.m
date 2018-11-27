-- Code (https://en.wikipedia.org/wiki/Szyma%C5%84ski%27s_algorithm)
-- 	PC -- Code
-- 	   -- # Entry protocol
-- 	00 -- flag[self] = 1				# Standing outside waiting room
-- 	01 -- await(all flag[1..N] = {0, 1, 2})		# Wait for open door
-- 	02 -- flag[self] = 3				# Standing in doorway
-- 	03 -- if any flag[1..N] = 1:			# Another process is waiting to enter
-- 	04 -- 	flag[self] = 2				# Waiting for other processes to enter
-- 	05 -- 	await(any flag[1..N] = 4)		# Wait for a process to enter and close the door
-- 	06 -- flag[self] = 4				# The door is closed
-- 	07 -- await(all flag[1..self-1] = {0, 1})	# Wait for everyone of lower ID to finish exit protocol
-- 	08 -- # Critical code
-- 	   -- # Exit protocol
-- 	09 -- await(all flag[self+1..N] = {0, 1, 4})	# Ensure everyone in the waiting room has
-- 	  -- 						# realized that the door is supposed to be closed
-- 	10 -- flag[self] = 0				# Leave. Reopen door if nobody is still in the waiting room

-- Constants and Variables

Const
	ProcCount: 6; -- Number of processes
	LineCount: 14; -- Number of lines of code

Type
	Pid: Scalarset(ProcCount);	-- Processor ID
	PC: 0..(LineCount-1);

Var
	flags: Array[Pid] of Scalarset(5);
	pcs: Array[Pid] of PC;

-- Rules
-- for transitioning from one line to the next
-- Each rule fire is an attempt to run a line of code and move on to the next
-- Sometimes they move on, sometimes they don't (await), sometimes they branch (if)

Ruleset p: Pid Do
	Rule "Line 00"
		(pcs[p] = 0)
	==>
		flags[p] := 1;
		pcs[p] := 1;
	Endrule;

	Rule "Line 01"
		(pcs[p] = 1)
		& (Forall p1: Pid Do
			(flags[p1] = 0) | (flags[p1] = 1) | (flags[p1] = 2)
		 Endforall)
	==>
		pcs[p] := 2;
	Endrule;

	Rule "Line 02"
		(pcs[p] = 2)
	==>
		flags[p] := 3;
		pcs[p] := 3;
	Endrule;

	Rule "Line 03 - branch 1"
		(pcs[p] = 3)
		& (Exists p1: Pid Do
			(flags[p1] = 1)
		Endexists)
	==>
		pcs[p] := 4;
	Endrule;

	Rule "Line 03 - branch 2"
		(pcs[p] = 3)
		& !(Exists p1: Pid Do
			(flags[p1] = 1)
		Endexists)
	==>
		pcs[p] := 6;
	Endrule;

	Rule "Line 04"
		(pcs[p] = 4)
	==>
		flags[p] := 2;
		pcs[p] := 5;
	Endrule;

	Rule "Line 05"
		(pcs[p] = 5)
		& (Exists p1: Pid Do
			(flags[p1] = 4))
	==>
		pcs[p] := 6;
	Endrule;

	Rule "Line 06"
		(pcs[p] = 6)
	==>
		flags[p] := 4;
		pcs[p] := 7;
	Endrule;

	Rule "Line 07"
		(pcs[p] = 7)
		& (Forall p1: Pid Do
			(p1 >= p)
			| (flags[p1] = 0)
			| (flags[p1] = 1)
		Endforall)
	==>
		pcs[p] := 8;
	Endrule;

	Rule "Line 08"
		(pcs[p] = 8)
	==>
		-- Critical code
		pcs[p] := 9;
	Endrule;

	Rule "Line 09"
		(pcs[p] = 9)
		& (Forall p1: Pid Do
			(p1 <= p)
			| (flags[p1] = 0)
			| (flags[p1] = 1)
			| (flags[p1] = 4)
		Endforall)
	==>
		pcs[p] := 10;
	Endrule;

	Rule "Line 10"
		(pcs[p] == 10)
	==>
		flags[p] := 0;
		pcs[p] := 0;
	Endrule;
Endruleset;

-- Startstate
Startstate

	-- Processes start out waiting outside the door
	For p: Pid Do
		pcs[p] := 0;
		flags[p] := 0;
	Endfor;

Endstartstate;

--------------------
-- Specification
--------------------

-- No two proceses can both be in the critical section
Invariant "Mutual exclusion"
	Forall p1: Pid; p2: Pid Do
		((pcs[p1] = 8 & pcs[p2] = 8) -> p1 = p2)
	Endforall
