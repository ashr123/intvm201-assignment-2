package il.ac.bgu.cs.formalmethodsintro.base;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.util.Util;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

import java.io.InputStream;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only.<br>
 * More about facade: <a href="http://www.vincehuston.org/dp/facade.html">http://www.vincehuston.org/dp/facade.html</a>.
 */
@SuppressWarnings("unused")
public class FvmFacade
{

	private static FvmFacade INSTANCE = null;
	final String LOC_EXIT = "";
	final String ACT_NOTHING = "";
	final String COND_TRUE = "";

	/**
	 * @return an instance of this class.
	 */
	public static FvmFacade get()
	{
		if (INSTANCE == null)
			INSTANCE = new FvmFacade();
		return INSTANCE;
	}

	/**
	 * Checks whether a transition system is action deterministic. I.e., if for
	 * any given p and α there exists only a single tuple (p,α,q) in →. Note
	 * that this must be true even for non-reachable states.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @return {@code true} iff the action is deterministic.
	 */
	public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts)
	{
		return ts.getInitialStates().size() < 2 &&
				ts.getStates().parallelStream()
						.noneMatch(state -> ts.getActions().parallelStream()
								.anyMatch(action -> post(ts, state, action).size() > 1));
	}

	/**
	 * Checks whether an action is ap-deterministic (as defined in class), in
	 * the context of a given {@link TransitionSystem}.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @return {@code true} iff the action is ap-deterministic.
	 */
	public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts)
	{
		return ts.getInitialStates().size() < 2 &&
				ts.getStates().parallelStream()
						.map(state -> post(ts, state))
						.allMatch(postStates -> postStates.size() == postStates.parallelStream()
								.map(ts::getLabel)
								.collect(Collectors.toSet())
								.size());
	}

	/**
	 * Checks whether an alternating sequence is an execution of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an execution of {@code ts}.
	 * @return {@code true} iff {@code e} is an execution of {@code ts}.
	 */
	public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
	{
		return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
	}

	/**
	 * Checks whether an alternating sequence is an execution fragment of a
	 * {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an execution fragment of
	 *            {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of
	 * {@code ts}.
	 */
	public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
	{
		if (e.isEmpty())
			return true;
		if (!ts.getStates().contains(e.head()))
			throw new StateNotFoundException(e.head());
		if (e.size() == 1)
			return true;
		final AlternatingSequence<A, S> eNext = e.tail();
		if (eNext.isEmpty())
			return false;
		if (!ts.getActions().contains(eNext.head()))
			throw new ActionNotFoundException(eNext.head());
		final AlternatingSequence<S, A> eNext2 = eNext.tail();
		if (eNext2.isEmpty())
			return false;
		if (!ts.getStates().contains(eNext2.head()))
			throw new StateNotFoundException(eNext2.head());
		if (ts.getTransitions().contains(new TSTransition<>(e.head(), eNext.head(), eNext2.head())))
			return isExecutionFragment(ts, eNext2);
		return false;
	}

	/**
	 * Checks whether an alternating sequence is an initial execution fragment
	 * of a {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be an initial execution
	 *            fragment of {@code ts}.
	 * @return {@code true} iff {@code e} is an execution fragment of
	 * {@code ts}.
	 */
	public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
	{
		if (!ts.getInitialStates().contains(e.head()))
		{
			return false;
		}

		return isExecutionFragment(ts, e);
	}

	/**
	 * Checks whether an alternating sequence is a maximal execution fragment of
	 * a {@link TransitionSystem}, as defined in class.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param <P> Type of atomic propositions.
	 * @param ts  The transition system being tested.
	 * @param e   The sequence that may or may not be a maximal execution fragment
	 *            of {@code ts}.
	 * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
	 */
	public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e)
	{
		return isStateTerminal(ts, e.last()) && isExecutionFragment(ts, e);
	}

	/**
	 * Checks whether a state in {@code ts} is terminal.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   The state being tested for terminality.
	 * @return {@code true} iff state {@code s} is terminal in {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s)
	{
		return post(ts, s).isEmpty();
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @return All the states in {@code Post(s)}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s)
	{
		if (!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
		return ts.getTransitions().parallelStream()
				.filter(tsTransition -> tsTransition.getFrom().equals(s))
				.map(TSTransition::getTo)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param c   States in {@code ts}.
	 * @return All the states in {@code Post(s)} where {@code s} is a member of
	 * {@code c}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c)
	{
		return c.parallelStream()
				.map(state -> post(ts, state))
				.flatMap(Set::parallelStream)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transition to from
	 * {@code s}, when action {@code a} is selected.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a)
	{
		if (!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
		return ts.getTransitions().parallelStream()
				.filter(tsTransition -> tsTransition.getFrom().equals(s) && tsTransition.getAction().equals(a))
				.map(TSTransition::getTo)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param c   Set of states in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transition to from any state
	 * in {@code c}, when action {@code a} is selected.
	 */
	public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a)
	{
		return c.parallelStream()
				.map(state -> post(ts, state, a))
				.flatMap(Set::parallelStream)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
	 */
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s)
	{
		if (!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
		return ts.getTransitions().parallelStream()
				.filter(tsTransition -> tsTransition.getTo().equals(s))
				.map(TSTransition::getFrom)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param ts  Transition system of {@code s}.
	 * @param c   States in {@code ts}.
	 * @return All the states in {@code Pre(s)} where {@code s} is a member of
	 * {@code c}, in the context of {@code ts}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c)
	{
		return c.parallelStream()
				.map(state -> pre(ts, state))
				.flatMap(Set::parallelStream)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param s   A state in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transitioned from, when in
	 * {@code s}, and the last action was {@code a}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a)
	{
		if (!ts.getStates().contains(s))
			throw new StateNotFoundException(s);
		return ts.getTransitions().parallelStream()
				.filter(tsTransition -> tsTransition.getTo().equals(s) && tsTransition.getAction().equals(a))
				.map(TSTransition::getFrom)
				.collect(Collectors.toSet());
	}

	/**
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @param c   Set of states in {@code ts}.
	 * @param a   An action.
	 * @return All the states that {@code ts} might transitioned from, when in
	 * any state in {@code c}, and the last action was {@code a}.
	 * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
	 */
	public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a)
	{
		return c.parallelStream()
				.map(state -> pre(ts, state, a))
				.flatMap(Set::parallelStream)
				.collect(Collectors.toSet());
	}

	/**
	 * Implements the {@code reach(TS)} function.
	 *
	 * @param <S> Type of states.
	 * @param <A> Type of actions.
	 * @param ts  Transition system of {@code s}.
	 * @return All states reachable in {@code ts}.
	 */
	public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts)
	{
		Set<S> visited = new HashSet<>();
		Deque<S> queue = new LinkedList<>();
		for (S s : ts.getInitialStates())
		{
			queue.add(s);
			while (!queue.isEmpty())
			{
				visited.add(s = queue.poll());
				post(ts, s).stream()
						.filter(n -> !visited.contains(n))
						.forEach(n ->
						{
							visited.add(n);
							queue.add(n);
						});
			}
		}
		return visited;
	}

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1> Type of states in the first system.
	 * @param <S2> Type of states in the first system.
	 * @param <A>  Type of actions (in both systems).
	 * @param <P>  Type of atomic propositions (in both systems).
	 * @param ts1  The first transition system.
	 * @param ts2  The second transition system.
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2)
	{
		return interleave(ts1, ts2, Collections.emptySet());
	}

	/**
	 * Compute the synchronous product of two transition systems.
	 *
	 * @param <S1>               Type of states in the first system.
	 * @param <S2>               Type of states in the first system.
	 * @param <A>                Type of actions (in both systems).
	 * @param <P>                Type of atomic propositions (in both systems).
	 * @param ts1                The first transition system.
	 * @param ts2                The second transition system.
	 * @param handShakingActions Set of actions both systems perform together.
	 * @return A transition system that represents the product of the two.
	 */
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions)
	{
		final TransitionSystem<Pair<S1, S2>, A, P> ts = new TransitionSystem<>();

		ts1.getStates()
				.forEach(s1 -> ts2.getStates().stream()
						.map(s2 -> new Pair<>(s1, s2))
						.forEach(pair ->
						{
							if (ts1.getInitialStates().contains(pair.getFirst()) &&
									ts2.getInitialStates().contains(pair.getSecond()))
								ts.addInitialState(pair); // I₁×I₂
							ts.addState(pair);
							final Consumer<P> pConsumer = label -> ts.addToLabel(pair, label);
							ts1.getLabel(pair.getFirst()).forEach(pConsumer);
							ts2.getLabel(pair.getSecond()).forEach(pConsumer); // S₁×S₂, AP₁∪AP₂, L(⟨s₁, s₂⟩)=L₁(s₁)∪L₂(s₂)
						}));

		ts.addAllActions(ts1.getActions());
		ts.addAllActions(ts2.getActions()); // Act₁∪Act₂

		handShakingActions.forEach(action -> ts1.getTransitions().stream()
				.filter(transitionTS1 -> transitionTS1.getAction().equals(action))
				.forEach(transitionTS1 -> ts2.getTransitions().stream()
						.filter(transitionTS2 -> transitionTS2.getAction().equals(action) &&
								transitionTS2.getAction().equals(transitionTS1.getAction()))
						.forEach(transitionTS2 -> ts.getStates().stream()
								.filter(pair -> pair.getFirst().equals(transitionTS1.getFrom()) &&
										pair.getSecond().equals(transitionTS2.getFrom()))
								.forEach(fromPair -> ts.getStates().stream()
										.filter(pair -> pair.getFirst().equals(transitionTS1.getTo()) &&
												pair.getSecond().equals(transitionTS2.getTo()))
										.map(toPair -> new TSTransition<>(fromPair, action, toPair))
										.forEach(ts::addTransition))))); /*→*/
		ts1.getTransitions().stream()
				.filter(transition -> !handShakingActions.contains(transition.getAction()))
				.forEach(transition -> ts.getStates().stream()
						.filter(pair -> pair.getFirst().equals(transition.getFrom()))
						.forEach(fromPair -> ts.getStates().stream()
								.filter(pair -> pair.getFirst().equals(transition.getTo()) &&
										pair.getSecond().equals(fromPair.getSecond()))
								.map(toPair -> new TSTransition<>(fromPair, transition.getAction(), toPair))
								.forEach(ts::addTransition))); /*→*/
		ts2.getTransitions().stream()
				.filter(transition -> !handShakingActions.contains(transition.getAction()))
				.forEach(transition -> ts.getStates().stream()
						.filter(pair -> pair.getSecond().equals(transition.getFrom()))
						.forEach(fromPair -> ts.getStates().stream()
								.filter(pair -> pair.getSecond().equals(transition.getTo()) &&
										pair.getFirst().equals(fromPair.getFirst()))
								.map(toPair -> new TSTransition<>(fromPair, transition.getAction(), toPair))
								.forEach(ts::addTransition))); /*→*/

		ts.setName(ts1.getName() + (handShakingActions.isEmpty() ? "⫼_∅" : "⫼_{" + handShakingActions + '}') + ts2.getName());

		return ts;
	}

	/**
	 * Creates a new {@link ProgramGraph} object.
	 *
	 * @param <L> Type of locations in the graph.
	 * @param <A> Type of actions of the graph.
	 * @return A new program graph instance.
	 */
	public <L, A> ProgramGraph<L, A> createProgramGraph()
	{
		return new ProgramGraph<>();
	}

	/**
	 * Interleaves two program graphs.
	 *
	 * @param <L1> Type of locations in the first graph.
	 * @param <L2> Type of locations in the second graph.
	 * @param <A>  Type of actions in BOTH GRAPHS.
	 * @param pg1  The first program graph.
	 * @param pg2  The second program graph.
	 * @return Interleaved program graph.
	 */
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2)
	{
		final ProgramGraph<Pair<L1, L2>, A> pg = createProgramGraph();

		pg1.getLocations()
				.forEach(l1 -> pg2.getLocations().stream()
						.map(l2 -> new Pair<>(l1, l2))
						.forEach(pair ->
						{
							pg.addLocation(pair);
							pg.setInitial(pair, pg1.getInitialLocations().contains(pair.getFirst()) && pg2.getInitialLocations().contains(pair.getSecond())); // I₁×I₂
						})); // Loc₁×Loc₂, Loc₀,₁×Loc₀,₂

		pg1.getTransitions()
				.forEach(transition -> pg.getLocations().stream()
						.filter(pair -> pair.getFirst().equals(transition.getFrom()))
						.forEach(fromPair -> pg.getLocations().stream()
								.filter(pair -> pair.getFirst().equals(transition.getTo()) &&
										pair.getSecond().equals(fromPair.getSecond()))
								.map(toPair -> new PGTransition<>(fromPair, transition.getCondition(), transition.getAction(), toPair))
								.forEach(pg::addTransition))); /*→*/

		pg2.getTransitions()
				.forEach(transition -> pg.getLocations().stream()
						.filter(pair -> pair.getSecond().equals(transition.getFrom()))
						.forEach(fromPair -> pg.getLocations().stream()
								.filter(pair -> pair.getSecond().equals(transition.getTo()) &&
										pair.getFirst().equals(fromPair.getFirst()))
								.map(toPair -> new PGTransition<>(fromPair, transition.getCondition(), transition.getAction(), toPair))
								.forEach(pg::addTransition))); /*→*/

		pg1.getInitalizations()
				.forEach(i1 -> pg2.getInitalizations().stream()
						.map(i2 ->
						{
							final List<String> concatList = new ArrayList<>(i1);
							concatList.addAll(i2);
							return concatList;
						})
						.forEach(pg::addInitalization));

		pg.setName(pg1.getName() + '‖' + pg2.getName());

		return pg;
	}

	/**
	 * Creates a {@link TransitionSystem} representing the passed circuit.
	 *
	 * @param c The circuit to translate into a {@link TransitionSystem}.
	 * @return A {@link TransitionSystem} representing {@code c}.
	 */
	public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c)
	{
		TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = new TransitionSystem<>();

		Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> states = new HashSet<>();
		Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> inits = new HashSet<>();

		Set<Set<String>> registersPowerSet = Util.powerSet(c.getRegisterNames());
		Set<Set<String>> inputsPowerSet = Util.powerSet(c.getInputPortNames());

		Set<Map<String, Boolean>> registersMaps = new HashSet<>();
		for (Set<String> registersSet : registersPowerSet)
		{
			Map<String, Boolean> registersMap = new HashMap<>();
			for (String register : c.getRegisterNames())
			{
				if (registersSet.contains(register))
					registersMap.put(register, true);
				else
					registersMap.put(register, false);
			}
			registersMaps.add(registersMap);
		}

		Set<Map<String, Boolean>> inputsMaps = new HashSet<>();
		for (Set<String> inputsSet : inputsPowerSet)
		{
			Map<String, Boolean> inputsMap = new HashMap<>();
			for (String input : c.getInputPortNames())
			{
				if (inputsSet.contains(input))
					inputsMap.put(input, true);
				else
					inputsMap.put(input, false);
			}
			inputsMaps.add(inputsMap);
		}

		/***
		 * Adding all the initial states and states.
		 */
		for (Map<String, Boolean> inputsMap : inputsMaps)
		{
			for (Map<String, Boolean> registersMap : registersMaps)
			{
				Pair<Map<String, Boolean>, Map<String, Boolean>> stateEntry = new Pair<>(inputsMap, registersMap);
				states.add(stateEntry);
				if (!stateEntry.getSecond().values().contains(true))
					inits.add(stateEntry);
			}
		}
		ts.addAllStates(states);
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> init : inits)
		    ts.addInitialState(init);

		/***
		 * Adding all the actions.
		 */
		ts.addAllActions(inputsMaps);

		/***
		 * Adding all the transitions.
		 */
		Set<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitions = new HashSet<>();
		for (Map<String, Boolean> action : ts.getActions())
			for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates())
				transitions.add(new TSTransition<>(state, action, new Pair<>(action, c.updateRegisters(state.first, state.second))));
		for (TSTransition transition : transitions)
			ts.addTransition(transition);

		Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> newReachableStates = reach(ts);
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : states)
		{
			if (!newReachableStates.contains(state))
			{
				Set<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitionsToRemove = new HashSet<>();
				for (TSTransition transition : transitions)
                    if (transition.getFrom().equals(state) || transition.getTo().equals(state))
                        transitionsToRemove.add(transition);
				for (TSTransition transitionToRemove : transitionsToRemove)
                    ts.removeTransition(transitionToRemove);
				ts.removeState(state);
			}
		}

		/***
		 * Adding all the atomic propositions.
		 */
		for (String input : c.getInputPortNames())
            ts.addAtomicProposition(input);
		for (String register : c.getRegisterNames())
            ts.addAtomicProposition(register);
		for (String output : c.getOutputPortNames())
            ts.addAtomicProposition(output);

		/***
		 * Adding all the labels.
		 */
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : ts.getStates())
		{
			for (String input : state.first.keySet())
                if (state.first.get(input))
                    ts.addToLabel(state, input);
			for (String register : state.second.keySet())
                if (state.second.get(register)) ts.addToLabel(state, register);
			Map<String, Boolean> outputs = c.computeOutputs(state.first, state.second);
			for (String output : outputs.keySet())
                if (outputs.get(output))
                    ts.addToLabel(state, output);
		}

		return ts;
	}

	/**
	 * Creates a {@link TransitionSystem} from a program graph.
	 *
	 * @param <L>           Type of program graph locations.
	 * @param <A>           Type of program graph actions.
	 * @param pg            The program graph to be translated into a transition system.
	 * @param actionDefs    Defines the effect of each action.
	 * @param conditionDefs Defines the conditions (guards) of the program
	 *                      graph.
	 * @return A transition system representing {@code pg}.
	 */
	public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
			ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs)
	{

		TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystem<>();

        /***
         * Adding all the actions.
         */
		for (PGTransition<L, A> transition : pg.getTransitions())
            if (!transition.getAction().equals(""))
                ts.addAction(transition.getAction());

        /***
         * Adding all the locations.
         */
		Set<Map<String, Object>> evals = new HashSet<>();
		for (List<String> actions : pg.getInitalizations())
		{
			Map<String, Object> eval = new HashMap<>();
			for (String action : actions)
                eval = ActionDef.effect(actionDefs, eval, action);
			evals.add(eval);
		}
		if (evals.isEmpty())
			evals.add(new HashMap<>());

        /***
         * Adding all the atomic propositions.
         */
		for (L initLoc : pg.getInitialLocations())
		{
			for (Map<String, Object> eval : evals)
			{
				Pair<L, Map<String, Object>> initState = new Pair<>(initLoc, eval);
				ts.addInitialState(initState);
				for (String var : eval.keySet())
                    ts.addAtomicProposition(var + " = " + eval.get(var));
			}
		}

        /***
         * Adding all the transitions.
         */
		Queue<Pair<L, Map<String, Object>>> states = new LinkedList<>(ts.getStates());
		while (!states.isEmpty())
		{
			Pair<L, Map<String, Object>> state = states.poll();
			for (PGTransition<L, A> transition : pg.getTransitions())
			{
				if (state.first.equals(transition.getFrom()) && ConditionDef.evaluate(conditionDefs, state.second, transition.getCondition()))
				{
					Map<String, Object> effect = ActionDef.effect(actionDefs, state.second, transition.getAction());
					if (effect != null)
					{
						Pair<L, Map<String, Object>> to = new Pair<>(transition.getTo(), effect);
						if (!ts.getStates().contains(to))
						{
							ts.addState(to);
							states.add(to);
						}
						if (ConditionDef.evaluate(conditionDefs, state.second, transition.getCondition()))
                            ts.addTransition(new TSTransition<>(state, transition.getAction(), to));
					}
				}
			}
		}

		Set<Pair<L, Map<String, Object>>> statesTag = new HashSet<>(ts.getStates());
		Set<Pair<L, Map<String, Object>>> reach = reach(ts);
		for (Pair<L, Map<String, Object>> state : statesTag)
            if (!reach.contains(state))
                ts.removeState(state);

        /***
         * Adding all the labeling.
         */
		for (Pair<L, Map<String, Object>> state : ts.getStates())
		{
			if (state.first instanceof ArrayList<?>)
			{
                //noinspection unchecked
                for (L l : (ArrayList<L>) state.first)
				{
					ts.addAtomicProposition(l.toString());
					ts.addToLabel(state, l.toString());
				}
			} else
			{
				ts.addAtomicProposition(state.first.toString());
				ts.addToLabel(state, state.first.toString());
			}

			for (PGTransition<L, A> transition : pg.getTransitions())
			{
				for (String key : state.second.keySet())
				{
					ts.addAtomicProposition(key + " = " + state.second.get(key));
					ts.addToLabel(state, key + " = " + state.second.get(key));
				}
			}
		}

		return ts;
	}

	/**
	 * Creates a transition system representing channel system {@code cs}.
	 *
	 * @param <L> Type of locations in the channel system.
	 * @param <A> Type of actions in the channel system.
	 * @param cs  The channel system to be translated into a transition system.
	 * @return A transition system representing {@code cs}.
	 */
	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs)
	{

		Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
		Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
		return transitionSystemFromChannelSystem(cs, actions, conditions);
	}

	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions)
	{
		ProgramGraph<List<L>, A> pg = new ProgramGraph<>();

		// first pg
		ProgramGraph<L, A> pg1 = cs.getProgramGraphs().get(0);
		for (L locij : pg1.getLocations())
		{
			// locations
			List<L> newLoc = new ArrayList<>();
			newLoc.add(locij);
			pg.addLocation(newLoc);

			// init
			if (pg1.getInitialLocations().contains(locij))
			{
				pg.setInitial(newLoc, true);
			}
		}

		// trans
		for (PGTransition<L, A> tran : pg1.getTransitions())
		{
			PGTransition<List<L>, A> newTran = new PGTransition<>(
					Arrays.asList(tran.getFrom()), tran.getCondition(), tran.getAction(), Arrays.asList(tran.getTo()));
			pg.addTransition(newTran);
		}

		// initializations
		for (List<String> inits : pg1.getInitalizations())
		{
			pg.addInitalization(inits);
		}

		// rest pg-s
		for (int i = 1; i < cs.getProgramGraphs().size(); i++)
		{
			ProgramGraph<L, A> pgi = cs.getProgramGraphs().get(i);
			pg = addProgramGraphs(pg, pgi);
		}

		Set<ActionDef> actionDefs = new LinkedHashSet<>();
		actionDefs.add(new ParserBasedInterleavingActDef());
		actionDefs.add(new ParserBasedActDef());
		Set<ConditionDef> conditionDefs = new HashSet<>();
		conditionDefs.add(new ParserBasedCondDef());

		TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts = transitionSystemFromProgramGraph(pg, actionDefs, conditionDefs);
		return ts;
//        throw new java.lang.UnsupportedOperationException();
	}

	private <L, A> ProgramGraph<List<L>, A> addProgramGraphs(ProgramGraph<List<L>, A> pgAll, ProgramGraph<L, A> pgi)
	{
		ProgramGraph<List<L>, A> pg = new ProgramGraph<>();
		// locations
		Set<List<L>> locations = new HashSet<>(pgAll.getLocations());
		for (List<L> locs : locations)
		{
			for (L locij : pgi.getLocations())
			{
				List<L> newLoc = new ArrayList<>(locs);
				newLoc.add(locij);
				pg.addLocation(newLoc);

				// init
				if (pgi.getInitialLocations().contains(locij) && pgAll.getInitialLocations().contains(locs))
				{
					pg.setInitial(newLoc, true);
				}
			}
		}

		// trans
		ParserBasedInterleavingActDef parser = new ParserBasedInterleavingActDef();
		Set<PGTransition<List<L>, A>> transitions = new HashSet<>(pgAll.getTransitions());
		for (PGTransition<List<L>, A> pgTransition : transitions)
		{
			if (!parser.isOneSidedAction(pgTransition.getAction().toString()))
			{
				for (L loc : pgi.getLocations())
				{
					List<L> from = new ArrayList<>(pgTransition.getFrom());
					from.add(loc);
					List<L> to = new ArrayList<>(pgTransition.getTo());
					to.add(loc);
					PGTransition<List<L>, A> newTran = new PGTransition<>(
							from, pgTransition.getCondition(), pgTransition.getAction(), to);
					pg.addTransition(newTran);
				}
			}
		}

		for (PGTransition<L, A> pgiTransition : pgi.getTransitions())
		{
			if (!parser.isOneSidedAction(pgiTransition.getAction().toString()))
			{
				for (List<L> loc : pgAll.getLocations())
				{
					List<L> from = new ArrayList<>(loc);
					from.add(pgiTransition.getFrom());
					List<L> to = new ArrayList<>(loc);
					to.add(pgiTransition.getTo());
					PGTransition<List<L>, A> newTran = new PGTransition<>(
							from, pgiTransition.getCondition(), pgiTransition.getAction(), to);
					pg.addTransition(newTran);
				}
			}
		}

		transitions = new HashSet<>(pgAll.getTransitions());
		for (PGTransition<List<L>, A> pgTransition : transitions)
		{
			for (PGTransition<L, A> pgiTransition : pgi.getTransitions())
			{
				A act = getHandShakeAction(pgTransition.getAction(), pgiTransition.getAction(), parser);
				if (act != null)
				{
					List<L> from = new ArrayList<>(pgTransition.getFrom());
					from.add(pgiTransition.getFrom());
					List<L> to = new ArrayList<>(pgTransition.getTo());
					to.add(pgiTransition.getTo());
					PGTransition<List<L>, A> newTransition = new PGTransition<>(
							from, mergeConditions(pgTransition.getCondition(), pgiTransition.getCondition()), act, to);
					pg.addTransition(newTransition);
				}
			}
		}

		// initializations
		Set<List<String>> inits = new HashSet<>(pgAll.getInitalizations());
		for (List<String> pgInits : inits)
		{
			for (List<String> pgiInits : pgi.getInitalizations())
			{
				List<String> init = new ArrayList<>(pgInits);
				init.addAll(pgiInits);
				pg.addInitalization(init);
			}
		}
		if (pgAll.getInitalizations().isEmpty())
		{
			for (List<String> init : pgi.getInitalizations())
			{
				pg.addInitalization(init);
			}
		}

		if (pgi.getInitalizations().isEmpty())
		{
			for (List<String> init : pgAll.getInitalizations())
			{
				pg.addInitalization(init);
			}
		}
		return pg;
	}

	private <A> A getHandShakeAction(A pgaction, A pgiaction, ParserBasedInterleavingActDef parser)
	{
		if (!(pgaction instanceof String) || !(pgiaction instanceof String))
			return null;
		if (!parser.isOneSidedAction(pgaction.toString()) || !parser.isOneSidedAction(pgiaction.toString()))
			return null;

		if (((String) pgaction).contains("?") && ((String) pgiaction).contains("!"))
		{
			String pgchannel = ((String) pgaction).substring(0, ((String) pgaction).indexOf("?"));
			String pgichannel = ((String) pgiaction).substring(0, ((String) pgiaction).indexOf("!"));
			if (pgchannel.equals(pgichannel))
				return (A) String.format("%s|%s", pgaction, pgiaction);
		}

		if (((String) pgaction).contains("!") && ((String) pgiaction).contains("?"))
		{
			String pgchannel = ((String) pgaction).substring(0, ((String) pgaction).indexOf("!"));
			String pgichannel = ((String) pgiaction).substring(0, ((String) pgiaction).indexOf("?"));
			if (pgchannel.equals(pgichannel))
			{
				return (A) String.format("%s|%s", pgaction, pgiaction);
			}
		}

		return null;
	}

	private String mergeConditions(String PGCondition, String PGiCondition)
	{
		if (PGCondition.length() == 0)
			return PGiCondition;
		if (PGiCondition.length() == 0)
			return PGCondition;
		return "(" + PGCondition + ") && (" + PGiCondition + ")";
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param filename The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception
	{
		return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaFile(filename));
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param nanopromela The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception
	{
		return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaString(nanopromela));
	}

	/**
	 * Construct a program graph from nanopromela code.
	 *
	 * @param inputStream The nanopromela code.
	 * @return A program graph for the given code.
	 * @throws Exception If the code is invalid.
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception
	{
		return programGraphFromNanoPromela(NanoPromelaFileReader.parseNanoPromelaStream(inputStream));
	}

	private ProgramGraph<String, String> programGraphFromNanoPromela(NanoPromelaParser.StmtContext nanopromela) throws Exception
	{
		ProgramGraph<String, String> pg = new ProgramGraph<>();
		Map<String, Set<PGTransition<String, String>>> locsToTransitions = new HashMap<>();
		sub(nanopromela, locsToTransitions);

		pg.addLocation(nanopromela.getText());
		Queue<String> locs = new LinkedList<>(pg.getLocations());
		while (!locs.isEmpty())
		{
			String loc = locs.poll();
			if (!loc.equals(""))
				for (PGTransition<String, String> transition : locsToTransitions.get(loc))
				{
					if (!pg.getLocations().contains(transition.getTo()))
					{
						pg.addLocation(transition.getTo());
						locs.add(transition.getTo());
					}
					pg.addTransition(transition);
				}
		}
		pg.setInitial(nanopromela.getText(), true);

		return pg;
	}


	private void sub(NanoPromelaParser.StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTransition)
	{
		if (subTransition.containsKey(stmt.getText()))
            return;

		Set<PGTransition<String, String>> transition = new HashSet<>();

		if (stmt.assstmt() != null || stmt.chanreadstmt() != null || stmt.chanwritestmt() != null || stmt.atomicstmt() != null || stmt.skipstmt() != null)
		{
			transition.add(new PGTransition<>(stmt.getText(), COND_TRUE, stmt.getText(), LOC_EXIT));
			subTransition.put(stmt.getText(), transition);
		} else if (stmt.ifstmt() != null)
            ifSub(stmt, subTransition, transition);
        else if (stmt.dostmt() != null)
            doSub(stmt, subTransition);
        else
            concatSub(stmt, subTransition);
	}

	private void ifSub(NanoPromelaParser.StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTransition, Set<PGTransition<String, String>> transition)
	{
		for (NanoPromelaParser.OptionContext option : stmt.ifstmt().option())
		{
			sub(option.stmt(), subTransition);
			for (PGTransition<String, String> tran : subTransition.get(option.stmt().getText()))
			{
				String condition = "(" + option.boolexpr().getText() + ") && (" + tran.getCondition() + ")";
				if (option.boolexpr().getText().equals(""))
					condition = "(" + tran.getCondition() + ")";
				if (tran.getCondition().equals(""))
					condition = "(" + option.boolexpr().getText() + ")";
				if (tran.getCondition().equals("") && option.boolexpr().getText().equals(""))
					condition = "";
				transition.add(new PGTransition<>(stmt.getText(), condition, tran.getAction(), tran.getTo()));
			}
		}
		subTransition.put(stmt.getText(), transition);
	}

	private void doSub(NanoPromelaParser.StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTransition)
	{
		StringBuilder falseCondition = new StringBuilder();
		for (NanoPromelaParser.OptionContext option : stmt.dostmt().option())
		{
			sub(option.stmt(), subTransition);
			String gi = option.boolexpr().getText();
			String notGi = "!(" + gi + ") && ";
			falseCondition.append(notGi);
			doTransition(subTransition, stmt.getText(), option.stmt().getText(), stmt.getText(), gi, new HashSet<>());
		}
		falseCondition = new StringBuilder("(" + falseCondition.substring(0, falseCondition.length() - 4) + ")");
		addTransition(subTransition, new PGTransition<>(stmt.getText(), falseCondition.toString(), ACT_NOTHING, LOC_EXIT));
	}

	private void concatSub(NanoPromelaParser.StmtContext stmt, Map<String, Set<PGTransition<String, String>>> subTransition)
	{
		NanoPromelaParser.StmtContext stmt1 = stmt.stmt(0);
		NanoPromelaParser.StmtContext stmt2 = stmt.stmt(1);
		sub(stmt1, subTransition);
		sub(stmt2, subTransition);
		concatenationTransition(subTransition, stmt.getText(), stmt1.getText(), stmt2.getText(), new HashSet<>());
	}

	private void addTransition(Map<String, Set<PGTransition<String, String>>> subTransition, PGTransition<String, String> transition)
	{
		if (!subTransition.containsKey(transition.getFrom()))
			subTransition.put(transition.getFrom(), new HashSet<>());
		Set<PGTransition<String, String>> transitions = subTransition.get(transition.getFrom());
		transitions.add(transition);
	}


	private void doTransition(Map<String, Set<PGTransition<String, String>>> subTransition, String stmt, String stmt1, String stmt2, String gi, Set<String> handled)
	{
		if (handled.contains(stmt1))
			return;
		handled.add(stmt1);
		for (PGTransition<String, String> transition : subTransition.get(stmt1))
		{
			String condition = "(" + gi + ") && (" + transition.getCondition() + ")";
			if (gi.equals(""))
				condition = "(" + transition.getCondition() + ")";
			if (transition.getCondition().equals(""))
				condition = "(" + gi + ")";
			if (transition.getCondition().equals("") && gi.equals(""))
				condition = "";
			String to = transition.getTo() + ";" + stmt2;
			if (transition.getTo().equals(""))
				to = stmt2;
			addTransition(subTransition, new PGTransition<>(stmt, condition, transition.getAction(), to));
			if (!transition.getTo().isEmpty())
				doTransition(subTransition, to, transition.getTo(), stmt2, COND_TRUE, handled);
		}
	}

	private void concatenationTransition(Map<String, Set<PGTransition<String, String>>> subTransition, String stmt, String stmt1, String stmt2, Set<String> handled)
	{
		if (handled.contains(stmt1))
			return;
		handled.add(stmt1);
		for (PGTransition<String, String> transition : subTransition.get(stmt1))
		{
			String to = transition.getTo() + ";" + stmt2;
			if (transition.getTo().equals(""))
				to = stmt2;
			addTransition(subTransition, new PGTransition<>(stmt, transition.getCondition(), transition.getAction(), to));
			if (!transition.getTo().isEmpty())
				concatenationTransition(subTransition, to, transition.getTo(), stmt2, handled);
		}
	}

	/**
	 * Creates a transition system from a transition system and an automaton.
	 *
	 * @param <Sts>  Type of states in the transition system.
	 * @param <Saut> Type of states in the automaton.
	 * @param <A>    Type of actions in the transition system.
	 * @param <P>    Type of atomic propositions in the transition system, which is
	 *               also the type of the automaton alphabet.
	 * @param ts     The transition system.
	 * @param aut    The automaton.
	 * @return The product of {@code ts} with {@code aut}.
	 */
	public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
	                                                                            Automaton<Saut, P> aut)
	{
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Verify that a system satisfies an omega regular property.
	 *
	 * @param <S>    Type of states in the transition system.
	 * @param <Saut> Type of states in the automaton.
	 * @param <A>    Type of actions in the transition system.
	 * @param <P>    Type of atomic propositions in the transition system, which is
	 *               also the type of the automaton alphabet.
	 * @param ts     The transition system.
	 * @param aut    A Büchi automaton for the words that do not satisfy the
	 *               property.
	 * @return A VerificationSucceeded object or a VerificationFailed object
	 * with a counterexample.
	 */
	public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
	                                                                          Automaton<Saut, P> aut)
	{
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
	 * Büchi Automaton (NBA).
	 *
	 * @param <L> Type of resultant automaton transition alphabet
	 * @param ltl The LTL formula represented as a parse-tree.
	 * @return An automaton A such that L_\omega(A)=Words(ltl)
	 */
	public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl)
	{
		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * A translation of a Generalized Büchi Automaton (GNBA) to a
	 * Nondeterministic Büchi Automaton (NBA).
	 *
	 * @param <L>    Type of resultant automaton transition alphabet
	 * @param mulAut An automaton with a set of accepting states (colors).
	 * @return An equivalent automaton with a single set of accepting states.
	 */
	public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut)
	{
		throw new java.lang.UnsupportedOperationException();
	}

}
