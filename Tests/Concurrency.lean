import Tests.Support
import Conc

/-!
# Concurrency suite (unit W1.1)

The checks of `packages/base/conc/docs/PLAN.md`, "Test milestones". Each
check states one contract of the package.

No answer depends on how the scheduler orders the tasks:

* A state that must hold *now* is read through a call that never parks:
  `trySend` on a full channel, `tryRecv` on an empty one.
* A check on a parked task arranges the events so that one answer is
  possible in every order.
* Timers run on the test clock. `TestClock.nextTimer` waits until the
  code under test arms its timer, so `advance` cannot run before it.

Three checks wait in real time. The production timer waits on its own
timer, with the margin stated there. The production deadline waits
20 ms. The thread count gives the parked tasks a moment to park.

The suite runs in `Async`, as the code under test does, and the runner
enters it once through `Async.run`.
-/

set_option autoImplicit false

namespace Tests

open Conc

/-- The OS threads of this process, from `/proc/self/status`. `none` off
Linux. -/
private def threadCount : IO (Option Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let line := (s.splitOn "\n").find? (·.startsWith "Threads:")
    return line.bind fun l => ((l.drop 8).toString.trimAscii.toString).toNat?
  catch _ => return none

/-- `Chan`: close, EOF, order, back-pressure, and parked senders. -/
private def chanChecks (r : Runner) : Async Unit := do
  -- A `recv` on an empty channel wakes by close with `none`, and the
  -- queue drains before EOF.
  do
    let c : Chan Nat ← Chan.new 4
    r.check "an empty open channel has no value ready" ((← c.tryRecv) == none)
    let got : OnceRef (Option (Option Nat)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do got.set (some (← c.recv))
    -- Nothing is ever sent, so the receiver can only answer through the
    -- close, whether it parks before the close or after it.
    c.close
    ts.joinAll
    r.check "close wakes a recv with none" ((← got.get) == some none)
    let d : Chan Nat ← Chan.new 4
    discard <| d.send 1
    d.close
    let first ← d.recv
    let second ← d.recv
    r.check "a queued value drains before EOF" (first == some 1 && second == none)

  -- A second close is a no-op, and a send after close fails.
  do
    let c : Chan Nat ← Chan.new 1
    c.close
    c.close
    r.check "a second close leaves the channel closed" (← c.isClosed)
    r.check "a send after close fails with .closed" (failsWith .closed (← c.send 7))
    r.check "a trySend after close is refused" (!(← c.trySend 7))

  -- Drain, then EOF: three values in send order, then none.
  do
    let c : Chan Nat ← Chan.new 3
    for v in [10, 20, 30] do discard <| c.send v
    c.close
    let a ← c.recv
    let b ← c.recv
    let d ← c.recv
    let e ← c.recv
    r.check "three values arrive in send order, then none"
      ([a, b, d, e] == [some 10, some 20, some 30, none])
    let c2 : Chan Nat ← Chan.new 3
    for v in [1, 2] do discard <| c2.send v
    r.check "drain returns the queued values in send order" ((← c2.drain) == [1, 2])
    r.check "drain leaves the channel empty" ((← c2.tryRecv) == none)

  -- Capacity back-pressure: a full channel refuses a value now, and a
  -- parked send completes once a receive frees the slot.
  do
    let c : Chan Nat ← Chan.new 1
    r.check "a channel with a free slot takes a value now" (← c.trySend 1)
    r.check "a full channel refuses a value now" (!(← c.trySend 2))
    let ts ← TaskSet.new
    ts.spawn do discard <| c.send 2
    -- The receive frees the slot. The parked send can only complete
    -- after it, so the values arrive in send order.
    let a ← c.recv
    ts.joinAll
    let b ← c.recv
    r.check "a receive frees the slot for the parked send" (a == some 1 && b == some 2)

  -- Three sends parked on a full channel wake by the close alone, with
  -- `.closed`, and no refused value enters the queue. Nobody receives
  -- before the join, so only the close can end the sends, whether they
  -- park before the close or after it. (`Std`'s own close leaves them
  -- parked: `Chan`, "Why a sender never parks inside `Std`".)
  do
    let c : Chan Nat ← Chan.new 1
    discard <| c.send 1
    let closedCount : OnceRef Nat ← OnceRef.new 0
    let ts ← TaskSet.new
    for v in [2, 3, 4] do
      ts.spawn do
        if failsWith .closed (← c.send v) then closedCount.update (· + 1)
    c.close
    ts.joinAll
    r.check "close alone wakes three parked sends with .closed" ((← closedCount.get) == 3)
    let first ← c.recv
    let second ← c.recv
    r.check "the queued value drains, and no refused value arrives"
      (first == some 1 && second == none)

  -- Two slots free at once wake two parked senders: the first sender
  -- that succeeds sends another signal.
  do
    let c : Chan Nat ← Chan.new 2
    discard <| c.send 1
    discard <| c.send 2
    let ts ← TaskSet.new
    for v in [3, 4] do ts.spawn do discard <| c.send v
    -- Two values out, by calls that never park: two slots free.
    let a ← c.tryRecv
    let b ← c.tryRecv
    ts.joinAll
    let rest ← c.drain
    r.check "two freed slots let both parked senders through"
      (a == some 1 && b == some 2 && (rest == [3, 4] || rest == [4, 3]))

/-- `select`: the first park wins, in both orders. -/
private def selectChecks (r : Runner) : Async Unit := do
  -- `select` takes the park that completes first, in both orders. Both
  -- channels get a value, and the second send waits until `select` has
  -- answered, so the first send is the only one `select` can see. The
  -- value of the losing channel stays in that channel.
  for first in ["a", "b"] do
    let a : Chan Unit ← Chan.new 1
    let b : Chan Unit ← Chan.new 1
    let answered : Chan Unit ← Chan.new 1
    let (early, late) := if first == "a" then (a, b) else (b, a)
    let ts ← TaskSet.new
    ts.spawn do
      discard <| early.send ()
      discard answered.recv
      discard <| late.send ()
    let won ← select #[Park.recv a fun _ => "a", Park.recv b fun _ => "b"]
    answered.close
    ts.joinAll
    r.check s!"select takes the park that completes first ({first} first)" (won == first)
    r.check s!"select leaves the later value in its channel ({first} first)"
      ((← late.tryRecv) == some () && (← early.tryRecv) == none)

/-- `TaskSet`: errors reach the owner, and the join waits for every
task. -/
private def taskChecks (r : Runner) : Async Unit := do
  -- A failed task gives its error to the owner at `joinAll`, and the
  -- other tasks still join.
  do
    let ts ← TaskSet.new
    let ran : OnceRef Bool ← OnceRef.new false
    ts.spawn (throw <| IO.userError "boom")
    ts.spawn (ran.set true)
    let surfaced ← try ts.joinAll; pure false catch _ => pure true
    r.check "a task error surfaces at joinAll" surfaced
    r.check "the other tasks join before the error surfaces" (← ran.get)

  -- `joinAll` returns only after a live task ends: the task can end only
  -- after the gate closes, and the gate closes in a second task.
  do
    let gate : Chan Unit ← Chan.new 1
    let ended : OnceRef Bool ← OnceRef.new false
    let ts ← TaskSet.new
    ts.spawn do
      discard gate.recv
      ended.set true
    ts.spawn gate.close
    ts.joinAll
    r.check "joinAll waits for a live task to end" (← ended.get)

  -- `joinAll` also joins a task that a task of the set spawns while the
  -- join runs. The child can only spawn after the parent starts, and the
  -- parent spawns it before it ends.
  do
    let ts ← TaskSet.new
    let childRan : OnceRef Bool ← OnceRef.new false
    ts.spawn do ts.spawn (childRan.set true)
    ts.joinAll
    r.check "joinAll joins a task spawned during the join" (← childRan.get)

  -- Several failures surface as one error that counts them.
  do
    let ts ← TaskSet.new
    for i in [0:3] do ts.spawn (throw <| IO.userError s!"boom {i}")
    let msg ← try ts.joinAll; pure "" catch e => pure (toString e)
    r.check s!"joinAll counts and names every failure ({msg})"
      (msg.startsWith "3 tasks failed" && (msg.splitOn "boom").length == 4)

  -- Past the bound, `joinAll` still counts every failure, and it names
  -- only the kept ones.
  do
    let ts ← TaskSet.new
    let n := maxTaskErrors + 24
    for _ in [0:n] do ts.spawn (throw <| IO.userError "boom")
    let msg ← try ts.joinAll; pure "" catch e => pure (toString e)
    r.check "joinAll counts the failures past the bound" (msg.startsWith s!"{n} tasks failed")
    r.check "joinAll names only the kept failures"
      ((msg.splitOn "boom").length == maxTaskErrors + 1)

  -- A join empties the report, so a second join finds no old error, and
  -- the set stays usable.
  do
    let ts ← TaskSet.new
    ts.spawn (throw <| IO.userError "boom")
    let first ← try ts.joinAll; pure false catch _ => pure true
    let second ← try ts.joinAll; pure false catch _ => pure true
    r.check "a join reports an error once" (first && !second)
    let ran : OnceRef Bool ← OnceRef.new false
    ts.spawn (ran.set true)
    ts.joinAll
    r.check "a set runs new tasks after a join" (← ran.get)

  -- Two joins park on one live task, and the close wakes both. The check
  -- is the outer join: it hangs when one of the two stays parked.
  do
    let gate : Chan Unit ← Chan.new 1
    let ts ← TaskSet.new
    ts.spawn (discard gate.recv)
    let joins ← TaskSet.new
    for _ in [0:2] do joins.spawn ts.joinAll
    gate.close
    joins.joinAll
    r.check "two joins of one set both return" true

  -- 10000 short tasks of one set: the set holds a count, and the join
  -- returns only when the count reaches 0.
  do
    let cell : OnceRef Nat ← OnceRef.new 0
    let ts ← TaskSet.new
    for _ in [0:10000] do ts.spawn (cell.update (· + 1))
    ts.joinAll
    r.check "joinAll waits for 10000 short tasks" ((← cell.get) == 10000)

/-- The unbounded channel and `Pipe`. -/
private def queueChecks (r : Runner) : Async Unit := do
  -- The unbounded channel takes any number of values without a park,
  -- keeps them in order, and still ends with EOF after a close.
  do
    let c : Chan Nat ← Chan.newUnbounded
    for v in [0:1000] do discard <| c.send v
    c.close
    let got ← c.drain
    r.check "an unbounded channel keeps 1000 values in order" (got == List.range 1000)
    r.check "an unbounded channel reads EOF after the drain" ((← c.recv) == none)

  -- `Pipe`: chunks arrive in write order, an empty chunk never arrives,
  -- a write into a closed pipe fails (an empty one too), and a read
  -- after the last chunk is EOF.
  do
    let p ← Pipe.new 2
    let ab := ByteArray.mk #[0x61, 0x62]
    let c := ByteArray.mk #[0x63]
    discard <| p.write ab
    r.check "a pipe drops an empty chunk" (succeedsWith () (← p.write ByteArray.empty))
    discard <| p.write c
    p.close
    r.check "a write into a closed pipe fails" (failsWith .closed (← p.write c))
    r.check "an empty write into a closed pipe fails too"
      (failsWith .closed (← p.write ByteArray.empty))
    let first ← p.read
    let second ← p.read
    let third ← p.read
    r.check "a pipe yields its chunks in write order, then EOF"
      (first == some ab && second == some c && third == none)

  -- A full pipe parks the writer until a read frees a slot.
  do
    let p ← Pipe.new 1
    discard <| p.write (ByteArray.mk #[1])
    let ts ← TaskSet.new
    ts.spawn do discard <| p.write (ByteArray.mk #[2])
    let first ← p.read
    ts.joinAll
    let second ← p.read
    r.check "a full pipe parks the writer until a read frees a slot"
      (first == some (ByteArray.mk #[1]) && second == some (ByteArray.mk #[2]))

/-- `OnceRef` under contention, and the thread cost of parked tasks. -/
private def sharedChecks (r : Runner) : Async Unit := do
  -- N tasks update one `OnceRef` M times each, and none is lost.
  do
    let n := 8
    let m := 2000
    let cell : OnceRef Nat ← OnceRef.new 0
    let ts ← TaskSet.new
    for _ in [0:n] do
      ts.spawn do
        for _ in [0:m] do cell.update (· + 1)
    ts.joinAll
    r.check s!"{n}x{m} OnceRef updates lose none" ((← cell.get) == n * m)

  -- A `set` survives concurrent `get`s. Readers read the cell a fixed
  -- number of times, so they end with one worker too. A writer sets
  -- each value in turn and reads it back. With one worker the tasks do
  -- not overlap and the check holds trivially.
  do
    let cell : OnceRef Nat ← OnceRef.new 0
    let lost : OnceRef Nat ← OnceRef.new 0
    let ts ← TaskSet.new
    for _ in [0:3] do
      ts.spawn do
        for _ in [0:200000] do discard (cell.get : BaseIO Nat)
    ts.spawn do
      for v in [1:200000] do
        cell.set v
        if (← cell.get) != v then lost.update (· + 1)
    ts.joinAll
    r.check "a set survives concurrent gets" ((← lost.get) == 0)

  -- Parked tasks hold no thread: 2000 tasks parked on one channel keep
  -- the process near its starting thread count, and one close wakes all.
  do
    let before ← threadCount
    let c : Chan Unit ← Chan.new 1
    let woke : OnceRef Nat ← OnceRef.new 0
    let ts ← TaskSet.new
    for _ in [0:2000] do
      ts.spawn do
        discard c.recv
        woke.update (· + 1)
    -- A parking sleep gives the tasks time to park. A blocking one would
    -- hold the pool worker that they need.
    let settle ← Park.sleep 200 ()
    select #[settle]
    let parked ← threadCount
    c.close
    ts.joinAll
    r.check "one close wakes 2000 parked tasks" ((← woke.get) == 2000)
    match before, parked with
    | some b, some p =>
      r.check s!"2000 parked tasks hold no thread ({b} threads before, {p} parked)"
        (p ≤ b + 16)
    | _, _ => r.skip "parked tasks hold no thread" "no /proc/self/status"

/-- `withinDeadline` on the test clock and the production clock. -/
private def deadlineChecks (r : Runner) : Async Unit := do
  -- `withinDeadline` closes what the work parks on, and the work ends
  -- on its own. A work that ends in time returns its value, and the
  -- call throws a fault of the work.
  do
    let tc ← TestClock.new
    let parkedOn : Chan Unit ← Chan.new 1
    let workEnded : OnceRef Bool ← OnceRef.new false
    let answer : OnceRef (Option (Except Error Unit)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do
      let res ← withinDeadline tc.clock 50 parkedOn.close do
        -- Nothing is ever sent on `parkedOn`: only the expiry ends this.
        discard parkedOn.recv
        workEnded.set true
      answer.set (some res)
    r.check "the deadline arms its timer" (← tc.nextTimer)
    tc.advance 50
    ts.joinAll
    r.check "withinDeadline reports the expiry"
      ((← answer.get).any (failsWith .deadlineExpired))
    r.check "the expiry closes the park, and the work ends on its own" (← workEnded.get)
    -- The clock never advances again, so these timers never fire. Only
    -- the work can win.
    let quick ← withinDeadline tc.clock 50 (pure ()) (pure 42)
    r.check "a work that ends in time returns its value" (succeedsWith 42 quick)
    let thrown ← try
        discard <| withinDeadline tc.clock 50 (pure ())
          (throw (IO.userError "fault") : Async Nat)
        pure false
      catch _ => pure true
    r.check "the call throws a fault of the work" thrown
    tc.close

  -- A work that ends with a value after the timer won: the value goes
  -- to `release`. Nothing is sent on `gate`, so the work can end only
  -- through the close of `onExpiry`, after the timer has won.
  do
    let tc ← TestClock.new
    let gate : Chan Unit ← Chan.new 1
    let released : OnceRef (Option Nat) ← OnceRef.new none
    let answer : OnceRef (Option (Except Error Nat)) ← OnceRef.new none
    let ts ← TaskSet.new
    ts.spawn do
      let res ← withinDeadline tc.clock 50 gate.close
        (do discard gate.recv; pure 7)
        (fun v => released.set (some v))
      answer.set (some res)
    r.check "the late-value deadline arms its timer" (← tc.nextTimer)
    tc.advance 50
    ts.joinAll
    r.check "a late value still answers the expiry"
      ((← answer.get).any (failsWith .deadlineExpired))
    r.check "a late value goes to release" ((← released.get) == some 7)
    tc.close

  -- A timer that is due at once (0 ms) races a work that ends at once.
  -- Either may win, but the answer and the teardown must agree: the
  -- value means `onExpiry` never ran, and the expiry means it did. A
  -- work that ended first and lost its value is the bug this rules out.
  do
    let tc ← TestClock.new
    let mut consistent := true
    for _ in [0:50] do
      let tornDown : OnceRef Bool ← OnceRef.new false
      let res ← withinDeadline tc.clock 0 (tornDown.set true) (pure 7)
      let torn ← tornDown.get
      consistent := consistent &&
        ((succeedsWith 7 res && !torn) || (failsWith .deadlineExpired res && torn))
    r.check "a tied race gives one answer, and the teardown agrees" consistent
    tc.close

  -- The production clock drives the same deadline: a short timer closes
  -- the park of the work, and a long one leaves a quick work alone.
  do
    let gate : Chan Unit ← Chan.new 1
    let expired ← withinDeadline Clock.system 20 gate.close gate.recv
    r.check "a production deadline closes the park and reports the expiry"
      (failsWith .deadlineExpired expired)
    let quick ← withinDeadline Clock.system 60000 (pure ()) (pure 42)
    r.check "a work that ends in time beats a production deadline" (succeedsWith 42 quick)

/-- The test clock and the production clock. -/
private def clockChecks (r : Runner) : Async Unit := do
  -- The test clock moves by the given step, a timer fires at the
  -- advanced time and not before, and `close` ends every park on it.
  do
    let tc ← TestClock.new
    let clock := tc.clock
    let timer ← clock.after 50
    tc.advance 49
    r.check "the test clock advances by the step" ((← clock.nowMs) == 49)
    -- `ready` completes at once, so the timer wins only if it has fired.
    let ready : Chan Unit ← Chan.new 1
    ready.close
    let early ← select #[timer.map fun () => true, Park.recv ready fun _ => false]
    r.check "a timer does not fire before its time" (!early)
    tc.advance 1
    r.check "a timer fires at the advanced time" (← select #[timer.map fun () => true])
    let now ← clock.after 0
    r.check "a timer of 0 ms fires at once" (← select #[now.map fun () => true])
    let pending ← clock.after 1000
    for _ in [0:3] do discard tc.nextTimer
    tc.close
    r.check "close fires a pending timer" (← select #[pending.map fun () => true])
    r.check "nextTimer answers false on a closed clock" (!(← tc.nextTimer))

  -- The production clock: a timer counts from `after`, and the `select`s
  -- that it loses do not restart it. A message arrives every 50 ms for
  -- 2 s, and each one wins a `select`. A 300 ms timer must still win
  -- once its time comes. A timer that restarted would never win, and the
  -- loop would end at the end of the messages.
  do
    let msgs : Chan Unit ← Chan.new 1
    let ts ← TaskSet.new
    ts.spawn do
      for _ in [0:40] do
        -- A parking sleep: a blocking `IO.sleep` here would hold a pool
        -- worker, which the code under test never does.
        let tick ← Park.sleep 50 ()
        select #[tick]
        discard <| msgs.send ()
      msgs.close
    let start ← Clock.system.nowMs
    let timer ← Clock.system.after 300
    let mut firedAt : Option Nat := none
    repeat
      let won ← select #[Park.recv msgs (fun o => if o.isSome then "msg" else "eof"),
        timer.map fun () => "timer"]
      if won == "timer" then
        firedAt := some ((← Clock.system.nowMs) - start)
        break
      if won == "eof" then break
    msgs.close
    ts.joinAll
    -- `after` fixes the due time, and it runs after the read of
    -- `start`, so the park cannot fire before `start + 300` on the
    -- `IO.monoMsNow` clock. libuv's cached loop time can end a sleep
    -- early. The park then arms a new sleep (`Wrap.RawPark.sleepUntil`).
    r.check s!"a production timer fires at its time under losing selects ({firedAt} ms)"
      (firedAt.any (· ≥ 300))

/-- `Alarm` on the test clock. -/
private def alarmChecks (r : Runner) : Async Unit := do
  -- The alarm fires at the due time, and a later `set` replaces the due
  -- time. Each due time arms one timer, so `nextTimer` before `advance`
  -- means the timer of that due time exists.
  do
    let tc ← TestClock.new
    let a ← Alarm.new
    let fired : Chan Nat ← Chan.new 4
    let ts ← TaskSet.new
    ts.spawn (a.run tc.clock fired.send)
    a.set 100
    r.check "the alarm arms a timer for its due time" (← tc.nextTimer)
    tc.advance 100
    r.check "the alarm fires at the due time" ((← fired.recv) == some 100)
    a.set 200
    r.check "the alarm arms a timer for the next due time" (← tc.nextTimer)
    a.set 150
    r.check "a later set arms a timer for the new due time" (← tc.nextTimer)
    tc.advance 50
    r.check "a later set replaces the due time" ((← fired.recv) == some 150)
    -- Only the close can end `run` now: no due time is left. The check
    -- is the join: it hangs when `run` does not end.
    a.close
    ts.joinAll
    r.check "close ends run" true
    tc.close

  -- An `.error` from `fire` ends `run` with no close. The check is the
  -- join again.
  do
    let tc ← TestClock.new
    let a ← Alarm.new
    let fired : Chan Nat ← Chan.new 1
    fired.close
    let ts ← TaskSet.new
    ts.spawn (a.run tc.clock fired.send)
    a.set 10
    r.check "the alarm arms a timer before the refused fire" (← tc.nextTimer)
    tc.advance 10
    ts.joinAll
    r.check "an error from fire ends run" true
    tc.close

/-- `Outcome`: the rule that joins the answer and the fault. -/
private def outcomeChecks (r : Runner) : Async Unit := do
  let fault := IO.userError "reset"
  let throws (o : Outcome Error) : Async Bool :=
    try discard o.answer; pure false catch _ => pure true

  -- The first fault stays, and it throws under an orderly answer.
  do
    let o : Outcome Error ← Outcome.new
    o.recordFault (IO.userError "first")
    o.recordFault (IO.userError "second")
    o.finish (.ok ())
    let msg ← try discard o.answer; pure "" catch e => pure (toString e)
    r.check "the first fault stays, and throws under an orderly answer"
      (msg == toString (IO.userError "first"))

  -- A protocol error stays the answer, over a fault.
  do
    let o : Outcome Error ← Outcome.new
    o.recordFault fault
    o.finish (.error .closed)
    r.check "a protocol error stays the answer over a fault" (failsWith .closed (← o.answer))

  -- A fault after the end is not recorded, for each kind of end.
  do
    let o : Outcome Error ← Outcome.new
    o.finish (.ok ())
    o.recordFault fault
    r.check "a fault after the loop's answer is not recorded" (!(← throws o))
    let c : Outcome Error ← Outcome.new
    c.markClosing
    c.recordFault fault
    c.finish (.ok ())
    r.check "a fault after the owner's close is not recorded" (!(← throws c))

  -- A failed write keeps the same rule, in its own slot, and it does
  -- not reach `answer`.
  do
    let o : Outcome Error ← Outcome.new
    o.recordWriteFault fault
    r.check "a failed write fills its slot" (← o.writeFault).isSome
    r.check "a failed write does not throw at answer" (!(← throws o))
    let late : Outcome Error ← Outcome.new
    late.markClosing
    late.recordWriteFault fault
    r.check "a failed write after the end records nothing" (← late.writeFault).isNone

  -- A session with no fault and no answer reads as orderly.
  do
    let o : Outcome Error ← Outcome.new
    r.check "an outcome with no answer reads as orderly" (succeedsWith () (← o.answer))

/-- The receives of a queue that holds `n` values, by recursion: each
step calls the next inside the bind of its receive. The shape of the
`partial def` read loops of the stack (`Ping.echoLoop`). -/
private partial def drainRec (c : Chan Nat) (sum : Nat) : Async Nat := do
  match ← c.recv with
  | some v => drainRec c (sum + v)
  | none => return sum

/-- `Wrap.await` takes the value of a finished task at once. A run of
ready values must still run in bounded stack, in a `repeat` loop and in
a recursive loop. -/
private def readyChecks (r : Runner) : Async Unit := do
  let n := 1000000
  -- A `repeat` loop: `Std`'s `forIn` takes each step by a tail call.
  do
    let c : Chan Nat ← Chan.newUnbounded
    for i in [0:n] do discard <| c.trySend i
    c.close
    let mut sum := 0
    repeat
      match ← c.recv with
      | some v => sum := sum + v
      | none => break
    r.check s!"a repeat loop takes {n} ready values" (sum == n * (n - 1) / 2)
  -- A recursive loop over the same run.
  do
    let c : Chan Nat ← Chan.newUnbounded
    for i in [0:n] do discard <| c.trySend i
    c.close
    r.check s!"a recursive loop takes {n} ready values" ((← drainRec c 0) == n * (n - 1) / 2)

def Concurrency.run (r : Runner) : IO Unit := do
  r.section "concurrency" "(packages/base/conc/docs/PLAN.md, test milestones)"
  let all : Async Unit := do
    chanChecks r
    selectChecks r
    taskChecks r
    queueChecks r
    sharedChecks r
    deadlineChecks r
    clockChecks r
    alarmChecks r
    outcomeChecks r
    readyChecks r
  all.run

end Tests
