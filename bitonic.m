-- How bitonic sort works
-- a bitonic sequence is one that has a minimum or maximum, and is monotonic on each side
-- 
-- half-cleaner: takes a bitonic sequence and results in two things: a bitonic sequence and a clean bitonic sequence
-- i.e. every element in the top half is at least as small as every element in the bottom half
-- and both are bitonic
-- by doing a divide and conquer on the remaining halves, the result will obviously be sorted
-- 
-- to get the input to be bitonic, do bitonic sort on the top half first
-- and do bitonic sort in reverse on the bottom half
-- 
-- to keep everything in the same direction (no mirroring required),
-- can replace the first half-cleaner in each size-step with a "cone"
-- i.e. flip the output locations of the bottom half of the half-cleaner
-- this flips the reversed output from the bottom
--
-- overall there should be k(k+1)/2 parallel steps (or k+1 choose 2), where k is log_2 n (n is the input size)


-- Constants and Variables

Const
	k: 4; -- log of the size of the input
	sz: 2^k-1 -- size of input
	m: 10000 -- maximum integer size

Type
	Line: 0..(sz-1); -- Line ID (array index)
	PC: 0..(k*(k+1)/2); -- Program counter
	INT: 0..m;
-- A comparator has 3 values: a PC on which it is triggered, and the indeces of both it's operands
-- Any comparator must have all equal PC values in each line it uses and itself before triggering
-- Additionally, no comparators should trigger before they have all been made
--	(a major speedup for multiset states)
	Comparator:	Record
				L[2]: Line; -- Lines associated
				pc: PC; -- PC on which to trigger
			End;

Var
	vals: Array[Line] of INT; -- value of each line
	pcs: Array[Line] of PC; -- program counter for each line
	queue: MultiSet[Comparator] -- Comparators queued
	eval: boolean; -- Has the comparator circuit been constructed yet?
	qpc: PC -- number of parallel rounds of Comparators placed
	-- epc: PC -- PC up to where queued Comparators have been evaluated


-- https://www.cs.ubc.ca/~ajh/courses/cpsc513/assign-token/User.Manual

-- Procedures

-- Execute a swap operation on INTs
procedure Swap(var a, b: INT);
var temp: INT;
begin
	temp := a;
	a := b;
	b := temp;
end;

-- Add a comparator
procedure addSwap(i, j: Line, pc: PC);
var c: Comparator;
begin
	c.L[0] := i;
	c.L[1] := j;
	c.pc := pc;
	MultisetAdd(c,queue);
end;

-- Create a half-cleaner
-- v is: is it the first half-cleaner in the divide and conquer step
procedure HalfClean(l, r: Line, v: Boolean)
var halfwidth, a, b: Line;
begin
	halfwidth := (r-l)/2;
	for i := 0 to halfwidth do
		a = l + i;
		if v then
			b = r - i;
		else
			b = l + halfwidth + i;
		endif;
		addSwap(a,b,qpc);
	endfor;
end;

procedure HalfCleanTall(width: Line, v: Boolean)
begin
	for sect := 0 to (sz/width) do -- for each district of the lines
		HalfClean(sect*sz,(sect+1)*sz-1,v);
	endfor;
end;

procedure Bitonic(width: Line); -- not declared as var, therefore read-only
var mid,a,b: Line;
var halfwidth: Line;
begin
	if width > 1 then
		halfwidth := width/2;
		Bitonic(halfwidth); -- sub-sort
		-- Merge sub-problems
		HalfCleanTall(width, True); -- v-shape
		qpc := qpc + 1;
		while halfwidth > 1 do
			HalfCleanTall(halfwidth, False); -- normal half-clean
			qpc := qpc + 1;
			halfwidth := halfwidth / 2;
		endwhile;
	endif;
end;

-- Rules

Rule "Construct bitonic sort circuit"
	eval == False
==>
	Bitonic(sz);
	eval := true;
Endrule;

Choose comp: queue Do
	Rule "Evaluate comparator"
		(pcs[comp.L[0]] == comp.pc) &
		(pcs[comp.L[1]] == comp.pc)
	==>
		Swap(vals[comp.L[0]], vals[comp.L[1]]);
		pcs[comp.L[0]] := pcs[comp.L[0]] + 1;
		pcs[comp.L[1]] := pcs[comp.L[1]] + 1;
	Endrule;
Endchoose;


-- Startstate
Startstate

	-- Set eval to False, guaranteeing that the circuit will be constructed before anything else
	eval := False;

Endstartstate;

--------------------
-- Specification
--------------------

-- Result is in increasing order
Invariant "Ordered"
	(eval &					-- circuit has been created
	MultisetCount(c:queue, True) = 0)	-- circuit has been executed
	->
	Forall l: Line Do
		(l = sz-1 |			-- every adjacent pair is in order
		(vals[l] < vals[l+1]))
	Endforall

-- No two simultaneous comparators operate on the same values
-- i.e. the resulting circuit can be run in parallel
Invariant "Mutex"
	(MultisetCount(c1:queue,
		MultisetCount(c2:queue,		-- for every distinct pair of comparators at the same PC
			(c1 != c2) &
			(c1.pc = c2.pc) &
			((c1.L[0] = c1.L[0])
				| (c1.L[0] = c1.L[1])
				| (c1.L[1] = c1.L[0])
				| (c1.L[1] = c1.L[1]))) -- no pair exists with conflicting inputs
			> 0)
		= 0)

-- Correct amount of time to run (k+1 choose 2)
Invariant "Time"
	(eval
	->
	qpc = k*(k+1)/2)
