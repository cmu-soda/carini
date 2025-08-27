----- Cache ------

CONSTANTS Address, Core, Value

VARIABLES memory, cache, modified, exclusive, shared, invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer

vars == <<memory, cache, modified, exclusive, shared, invalid, proc_read, proc_write, bus_in_use, bus_read, bus_read_for_ownership, bus_upgrade, bus_transfer>>

Init ==
    /\ memory \in [Address -> Value]
    /\ cache \in [Core -> Address -> Value]
    /\ modified = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ exclusive = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ shared = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ invalid = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ proc_write = [c \in Core |-> [a \in Address |-> [v \in Value |-> FALSE]]]
    /\ bus_in_use = FALSE
    /\ bus_read = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_read_for_ownership = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_upgrade = [c \in Core |-> [a \in Address |-> FALSE]]
    /\ bus_transfer = [v \in Value |-> FALSE]

IssueProcReadInvalid(c, a) ==
    /\ invalid[c][a]
    /\ ~bus_in_use
    /\ bus_in_use' = TRUE
    /\ proc_read' = [proc_read EXCEPT![c][a] = ?]
    /\ bus_read' = [

transition issue_proc_read_invalid(c: core, a: address)
  modifies bus_in_use, proc_read, bus_read
  invalid(c, a) &
  !bus_in_use &
  new(bus_in_use) &
  (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) | C = c & A = a) &
  (forall C, A. new(bus_read(C, A)) <-> bus_read(C,A) | C != c & A = a)

transition do_bus_read_invalid(c: core, a: address)
  modifies bus_read
  bus_read(c, a) &
  invalid(c, a) &
  (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a))

transition do_bus_read_valid(c: core, a: address, v: value)
  modifies bus_read, modified, exclusive, shared, bus_transfer, memory
  bus_read(c, a) &
  !invalid(c, a) &
  cache(c, a) = v &
  (forall C, A. new(bus_read(C, A)) <-> bus_read(C, A) & !(C = c & A = a)) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
  (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
  (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
  (modified(c, a) ->  # write back
    (forall A.
       (A != a ->
         (new(memory(A)) = memory(A)))) &
     (new(memory(a)) = v)) &
  (!modified(c, a) ->
    (forall A. new(memory(A)) = memory(A))) &
  (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)

transition complete_proc_read_invalid_shared(c: core, a: address, v: value)
  modifies invalid, shared, bus_transfer, cache, bus_in_use, proc_read
  invalid(c, a) &
  proc_read(c, a) &
  bus_transfer(v) &
  (forall C, A. !bus_read(C, A)) &
  (forall V. !new(bus_transfer(V))) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) | C = c & A = a) &
  (forall C, A.
     !(C = c & A = a) ->
     (new(cache(C, A)) = cache(C, A))) &
  new(cache(c, a)) = v &
  !new(bus_in_use) &
  (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))

transition complete_proc_read_invalid_exclusive(c: core, a: address, v: value)
  modifies invalid, exclusive, cache, bus_in_use, proc_read
  invalid(c, a) &
  proc_read(c, a) &
  (forall V. !bus_transfer(V)) &
  (forall C, A. !bus_read(C, A)) &
  memory(a) = v &

  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
  (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) | C = c & A = a) &
  (forall C, A.
     !(C = c & A = a) ->
     (new(cache(C, A)) = cache(C, A))) &
  new(cache(c, a)) = v &
  !new(bus_in_use) &
  (forall C, A. new(proc_read(C, A)) <-> proc_read(C, A) & !(C = c & A = a))

transition issue_proc_write_invalid(c: core, a: address, v: value)
  modifies bus_in_use, proc_write, bus_read_for_ownership
  invalid(c, a) &
  !bus_in_use &
  new(bus_in_use) &
  (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) | C = c & A = a & V = v) &
  (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C,A) | C != c & A = a)

transition do_bus_read_for_ownership_invalid(c: core, a: address)
  modifies bus_read_for_ownership
  bus_read_for_ownership(c, a) &
  invalid(c, a) &
  (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a))

transition do_bus_read_for_ownership_valid(c: core, a: address, v: value)
  modifies bus_read_for_ownership, modified, exclusive, shared, invalid, bus_transfer, memory
  bus_read_for_ownership(c, a) &
  !invalid(c, a) &
  cache(c, a) = v &
  (forall C, A. new(bus_read_for_ownership(C, A)) <-> bus_read_for_ownership(C, A) & !(C = c & A = a)) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
  (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
  (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
  (modified(c, a) ->  # write back
    (forall A.
       (A != a ->
         (new(memory(A)) = memory(A)))) &
     (new(memory(a)) = v)) &
  (!modified(c, a) ->
    (forall A. new(memory(A)) = memory(A))) &
  (forall V. new(bus_transfer(V)) <-> bus_transfer(V) | V = v)

transition complete_proc_write_invalid(c: core, a: address, v: value)
  modifies invalid, modified, bus_transfer, cache, bus_in_use, proc_write
  invalid(c, a) &
  proc_write(c, a, v) &
  (forall C, A. !bus_read_for_ownership(C, A)) &
  (forall V. !new(bus_transfer(V))) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) & !(C = c & A = a)) &
  (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
  (forall C, A.
     !(C = c & A = a) ->
     (new(cache(C, A)) = cache(C, A))) &
  new(cache(c, a)) = v &
  !new(bus_in_use) &
  (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v))

transition proc_write_exclusive(c: core, a: address, v: value)
  modifies exclusive, modified, cache
  exclusive(c, a) &
  !bus_in_use &
  (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
  (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
  (forall C, A.
     !(C = c & A = a) ->
     (new(cache(C, A)) = cache(C, A))) &
  new(cache(c, a)) = v

transition issue_proc_write_shared(c: core, a: address, v: value)
  modifies bus_in_use, proc_write, bus_upgrade
  shared(c, a) &
  !bus_in_use &
  new(bus_in_use) &
  (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) | C = c & A = a & V = v) &
  (forall C, A. new(bus_upgrade(C, A)) <-> bus_upgrade(C,A) | C != c & A = a)

transition do_bus_upgrade(c: core, a: address)
  modifies bus_upgrade, shared, invalid
  bus_upgrade(c, a) &
  (forall C, A. new(bus_upgrade(C, A)) <-> bus_upgrade(C, A) & !(C = c & A = a)) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a))

transition complete_proc_write_shared(c: core, a: address, v: value)
  modifies bus_in_use, proc_write, cache, shared, modified
  shared(c, a) &
  proc_write(c, a, v) &
  (forall C, A. !bus_upgrade(C, A)) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
  (forall C, A. new(modified(C, A)) <-> modified(C, A) | C = c & A = a) &
  (forall C, A.
     !(C = c & A = a) ->
     (new(cache(C, A)) = cache(C, A))) &
  new(cache(c, a)) = v &
  (forall C, A, V. new(proc_write(C, A, V)) <-> proc_write(C, A, V) & !(C = c & A = a & V = v)) &
  !new(bus_in_use)

transition evict_modified(c: core, a: address)
  modifies memory, modified, invalid
  !bus_in_use &
  modified(c, a) &
  (forall A.
    (A != a ->
     (new(memory(A)) = memory(A)))) &
  new(memory(a)) = cache(c, a) &  # write back
  (forall C, A. new(modified(C, A)) <-> modified(C, A) & !(C = c & A = a)) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a)

transition evict_exclusive_or_shared(c: core, a: address)
  modifies exclusive, shared, invalid
  !bus_in_use &
  (exclusive(c, a) | shared(c, a)) &
  (forall C, A. new(exclusive(C, A)) <-> exclusive(C, A) & !(C = c & A = a)) &
  (forall C, A. new(shared(C, A)) <-> shared(C, A) & !(C = c & A = a)) &
  (forall C, A. new(invalid(C, A)) <-> invalid(C, A) | C = c & A = a)

safety !invalid(C, A) & !modified(C, A) -> cache(C, A) = memory(A)

