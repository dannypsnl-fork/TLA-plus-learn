-------------------------------- MODULE wire --------------------------------
EXTENDS TLC, Integers

People == {"alice", "bob"}
Money == 1..10
NumberTransfers == 2

(* --algorithm wire
variables
  acct \in [People -> Money];

define
  NoOverdrafts ==
    \A p \in People:
      acct[p] >= 0
end define;

process wire \in 1..NumTransfers
variable
  amnt \in 1..5;
  from \in People;
  to \in People
begin
  Check:
    if acct[from] >= amnt then
      Withdraw:
        acct[from] := acct[from] - amnt;
      Deposit:
        acct[to] := acct[to] + amnt;
    end if;
end process;
end algorithm *)
=============================================================================
\* Modification History
\* Last modified Thu Jul 21 19:38:28 CST 2022 by dannypsnl
\* Created Thu Jul 21 19:32:45 CST 2022 by dannypsnl
