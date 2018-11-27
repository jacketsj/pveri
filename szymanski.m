-- Murphi Model of a Simplified Version of TokenB Token Coherence
-- Alan J. Hu, 2014-Oct-2
--
--

Const
  ProcCount: 6;

Type
  Pid: Scalarset(ProcCount);  -- Processor ID
  ProcState: Record
              state: Enum{LEAVE, OUTSIDE, WAITING, DOORWAY, CLOSEDOOR, CRITICAL}
	    End;

Var
  procs: Array[Pid] of ProcState;
  flags: Array[Pid] of 0..4;

--------------------
-- Rules
--------------------

Ruleset p: Pid Do
  Rule "Waiting for open door"
    (Forall p1: Pid Do
      (flags[p1] == 0) | (flags[p1] == 1) | (flags[p1] == 2)
     Endforall)
  ==>
    flags[p] = 3;
    procs[p].state = DOORWAY;
  Endrule;

  Rule "Another process is waiting to enter"
    (Exists p1: Pid Do
      (p != p1) & (flags[p1] == 1)
     Endexists)
    ==>
      flags[p] = 2;
      procs[p].state = WAITING;
  Endrule;

  Rule "No other process is waiting to enter"
    !(Exists p1: Pid Do
       (p != p1) & (flags[p1] == 1)
      Endexists) & (flags[p] == 1)
    ==>
      flags[p] = 4;
      procs[p].state = CLOSEDOOR;
  Endrule;

  Rule "Another process has closed the door"
    (Exists p1: Pid Do
      (p != p1) & (flags[p1] == 4)
     Endexists)
    ==>
      flags[p] = 4;
      procs[p].state = CLOSEDOOR;
    Endrule;

  Rule "Waiting for lower ID processes to finish"
    

Ruleset p: Pid Do
  Ruleset a: Address Do

    Rule "Request Shared"
      (procs[p].cache[a].state = Invalid) &
      -- Make sure enough room in network for request
      (Forall p1: Pid Do
	(MultisetCount(i: toCaches[p1], TRUE) < BufferDepth)
       Endforall) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Broadcast(ReqS, p, UNDEFINED, False, a, UNDEFINED);
      -- Notice how I used UNDEFINED here, since the message doesn't
      -- need to contain tokens or a value.  Leaving these undefined
      -- results in a smaller set of reachable states (since the
      -- verifier doesn't explore states with different values of these.
    Endrule;

    Rule "Request Exclusive"
      (procs[p].cache[a].state != Modified) &
      -- Make sure enough room in network for request
      (Forall p1: Pid Do
	(MultisetCount(i: toCaches[p1], TRUE) < BufferDepth)
       Endforall) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Broadcast(ReqM, p, UNDEFINED, False, a, UNDEFINED);
    Endrule;

    Rule "Evict Clean Cache Line"
      (procs[p].cache[a].state = Shared) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      procs[p].cache[a].state := Invalid;
      SendMem(TokensOnly, UNDEFINED, procs[p].cache[a].tokens, False, a, UNDEFINED);
      procs[p].cache[a].tokens := 0;
    Endrule;

    Rule "Evict Owned or Modified Cache Line"
      ((procs[p].cache[a].state = Owned) | (procs[p].cache[a].state = Modified)) &
      (MultisetCount(i: toMem, TRUE) < BufferDepth)
    ==>
      Alias me: procs[p].cache[a] Do
        me.state := Invalid;
        SendMem(TokensData, UNDEFINED, me.tokens, True, a, me.v);
        me.tokens := 0;
      Endalias;
    Endrule;

    Ruleset v: Value Do
      Rule "Write to Dirty Data"
	-- ***** OBVIOUS BUG *****
        --(procs[p].cache[a].state = Shared)	-- This line is wrong.
        (procs[p].cache[a].state = Modified)	-- This is what it should be.
      ==>
	procs[p].cache[a].v := v;
      Endrule;
      Rule "Write to Clean Data"
	-- If I have all tokens, I can modify the data.
	(procs[p].cache[a].state != Modified) &
        (procs[p].cache[a].tokens = TokensPerAddress)
      ==>
	procs[p].cache[a].state := Modified;
	procs[p].cache[a].v := v;
      Endrule;
    Endruleset;

  Endruleset;
Endruleset;


-- For the network, it's easiest to get a valid message from the multiset
-- using the Choose command, and then do whatever action is needed to
-- process that message.  In our protocol, we have a separate channel
-- to each cache, as well as one to memory.

-- You use Choose sort of like Alias or Ruleset.  For example:
-- Choose i: upchannel Do
--   ...
-- Endchose;
-- allows you to refer to upchannel[i], within the scope of the Choose
-- statement, to get an arbitrary message in upchannel.
-- You can use the Send procedures I've given you to see how to add
-- things to multisets.  To remove them, use the MultiSetRemove statement.
-- For example, the following chooses an arbitrary message from upchannel
-- and deletes it.
-- Choose i: upchannel Do
--   Rule "Delete a random message"
--     True -- This rule is always enabled
--   ==>
--     MultiSetRemove(i, upchannel);
--   Endrule;
-- Endchoose;

-- Note that there appears to be a Murphi bug relating Choose and Alias.
-- If you get weird error messages when using an Alias within a Choose,
-- try moving the Alias to within the action part of the rule:
-- Choose i: upchannel Do
--   Rule "Delete a random message"
--     True -- This rule is always enabled
--   ==>
--     Alias foobar: upchannel Do
--       MultiSetRemove(i, foobar);
--     Endalias;
--   Endrule;
-- Endchoose;

Ruleset p: Pid Do
  Choose i: toCaches[p] Do
    Alias msg: toCaches[p][i] Do

      Rule "Processor gets ReqS"
        (msg.msg_type = ReqS) &
	(MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          if mycache.tokens > 0 then
	    if (mycache.state = Modified) | (mycache.state = Owned) then
              if mycache.tokens = 1 then
                SendCache(TokensData, msg.from, UNDEFINED, 1, True, msg.a, mycache.v);
              else
                SendCache(TokensData, msg.from, UNDEFINED, 1, False, msg.a, mycache.v);
	      endif;
	      mycache.tokens := mycache.tokens - 1;
	      mycache.state := Owned;
	    endif;
	    if mycache.tokens = 0 then
	      mycache.state := Invalid;
	      Undefine mycache.v;
	      -- Note that I Undefine the value in the cache, since this
	      -- isn't needed anymore (the entry is Invalid).  This keeps
	      -- Murphi from exploring states with different leftover values
	      -- here, reducing the size of the state space.
	    endif;
          endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets ReqM"
        (msg.msg_type = ReqM) &
	(MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          if mycache.tokens > 0 then
	    if (mycache.state = Modified) | (mycache.state = Owned) then
	      SendCache(TokensData, msg.from, UNDEFINED, mycache.tokens, True, msg.a, mycache.v);
	    else
	      SendCache(TokensOnly, msg.from, UNDEFINED, mycache.tokens, False, msg.a, UNDEFINED);
	    endif;
	    mycache.tokens := 0;
	    mycache.state := Invalid;
	    Undefine mycache.v;
          endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets Tokens without Data"
        msg.msg_type = TokensOnly
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          mycache.tokens := mycache.tokens + msg.tokens;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

      Rule "Processor gets Tokens with Data"
        msg.msg_type = TokensData
      ==>
	Alias mycache: procs[p].cache[msg.a] Do
          mycache.tokens := mycache.tokens + msg.tokens;
	  mycache.v := msg.d;
          if msg.owner then
	    mycache.state := Owned;
          endif;
	  if mycache.state = Invalid then
	    mycache.state := Shared;
	  endif;
	Endalias;
        MultisetRemove(i, toCaches[p]);
      Endrule;

    Endalias;
  Endchoose;
Endruleset;

Choose i: toMem Do
  Alias msg: toMem[i] Do

    Rule "Memory gets ReqS"
      (msg.msg_type = ReqS) &
      (MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
    ==>
      if mem[msg.a].owner then
        -- This is only my problem if I'm the owner.
        if mem[msg.a].tokens > 1 then
	  -- Send data, but retain ownership.
	  SendCache(TokensData, msg.from, UNDEFINED, 1, False, msg.a, mem[msg.a].v);
	  mem[msg.a].tokens := mem[msg.a].tokens - 1;
	elsif mem[msg.a].tokens = 1 then
	  -- My last token.  Send data as well as ownership.
	  SendCache(TokensData, msg.from, UNDEFINED, 1, True, msg.a, mem[msg.a].v);
	  mem[msg.a].tokens := mem[msg.a].tokens - 1;
	  mem[msg.a].owner := False;
        endif;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets ReqM"
      (msg.msg_type = ReqM) &
      (MultisetCount(i: toCaches[msg.from], TRUE) < BufferDepth)
    ==>
      if mem[msg.a].tokens > 0 then
	if mem[msg.a].owner then
	  SendCache(TokensData, msg.from, UNDEFINED, mem[msg.a].tokens, True, msg.a, mem[msg.a].v);
	else
	  SendCache(TokensOnly, msg.from, UNDEFINED, mem[msg.a].tokens, False, msg.a, UNDEFINED);
	endif;
	mem[msg.a].tokens := 0;
	mem[msg.a].owner := False;
	Undefine mem[msg.a].v;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets Tokens without Data"
      msg.msg_type = TokensOnly
    ==>
      mem[msg.a].tokens := mem[msg.a].tokens + msg.tokens;
      MultisetRemove(i, toMem);
    Endrule;

    Rule "Memory gets Tokens with Data"
      msg.msg_type = TokensData
    ==>
      mem[msg.a].tokens := mem[msg.a].tokens + msg.tokens;
      mem[msg.a].v := msg.d;
      if msg.owner then
	mem[msg.a].owner := True;
      endif;
      MultisetRemove(i, toMem);
    Endrule;

  Endalias;
Endchoose;

-- This defines the start states
Startstate

  -- Processes start out waiting outside the door
  For p: Pid Do
    procs[p].state := OUTSIDE;
    flags[p] = 1
  Endfor;

Endstartstate;

--------------------
-- Specification
--------------------
-- Here's an example property to check.  You can (and should) put down
-- additional specs here as well.  Just use the Invariant statement to
-- add other properties to check.

-- Also, it's often handy to use Assert statements within the rules
-- to check that the model is behaving as you expect.

-- Shared entries must agree with each other.
    Invariant "Shared entries must agree"
      Forall a: Address Do
	Forall p1: Pid; p2: Pid Do
	  ((procs[p1].cache[a].state = Shared)
	  & (procs[p2].cache[a].state = Shared))
	  -> (procs[p1].cache[a].v = procs[p2].cache[a].v)
	Endforall
      Endforall;

    Invariant "Always one owner per block"
      Forall a: Address Do
        Forall p1: Pid; p2: Pid Do
          ((procs[p1].cache[a].state = Owned)
          & (procs[p2].cache[a].state = Owned))
          -> ((p1 = p2) & (mem[a].owner = False))
        Endforall
      Endforall;

    Invariant "Zero tokens means invalid"
      Forall a: Address Do
        Forall p1: Pid Do
          (procs[p1].cache[a].tokens = 0)
          -> (procs[p1].cache[a].state = Invalid)
        Endforall
      Endforall;

    Invariant "All tokens means Owner or Modified"
      Forall a: Address Do
        Forall p1: Pid Do
          (procs[p1].cache[a].tokens = TokensPerAddress)
          -> ((procs[p1].cache[a].state = Owned) | (procs[p1].cache[a].state = Modified))
        Endforall
      Endforall;

    Invariant "Memory address with no tokens cannot be owner"
      Forall a: Address Do
        (mem[a].tokens = 0)
        -> (mem[a].owner = False)
      Endforall;

--    Invariant "Sum of all tokens per address does not change"
--      Forall a: Address Do
--        sumTokens := mem[a].tokens;
--        Forall p1: Pid Do
--          sumTokens := sumTokens + procs[p1].cache[a].tokens;
--        Endforall
--        (True)
--        -> (sumTokens = TokensPerAddress)
--      Endforall;
