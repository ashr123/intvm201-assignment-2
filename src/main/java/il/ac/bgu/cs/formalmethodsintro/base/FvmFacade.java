package il.ac.bgu.cs.formalmethodsintro.base;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.FairnessCondition;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.*;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.util.Util;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationSucceeded;

import java.io.InputStream;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.*;

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
				       .distinct() // ??? should be more efficient
				       .allMatch(postStates -> postStates.size() == postStates.parallelStream()
						       .map(ts::getLabel)
						       .distinct()
						       .count());
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
		return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
//		throw new java.lang.UnsupportedOperationException();
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
						.filter(Predicate.not(visited::contains))
						.peek(visited::add)
						.forEach(queue::add);
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
		return interleave(ts1, ts2, Set.of());
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
	 * @param circuit The circuit to translate into a {@link TransitionSystem}.
	 * @return A {@link TransitionSystem} representing {@code circuit}.
	 */
	public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit circuit)
	{
		TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = new TransitionSystem<>();

		Set<Map<String, Boolean>> registersMaps = Util.powerSet(circuit.getRegisterNames()).parallelStream()
				.map(registersSet -> circuit.getRegisterNames().parallelStream()
						.collect(Collectors.toMap(Function.identity(), registersSet::contains, (a, b) -> b)))
				.collect(Collectors.toSet());

		// Adding all the actions.
		ts.addAllActions(Util.powerSet(circuit.getInputPortNames()).stream()
				.map(inputsSet -> circuit.getInputPortNames().stream()
						.collect(Collectors.toMap(Function.identity(), inputsSet::contains, (a, b) -> b)))
				.collect(Collectors.toSet()));

		// Adding all the initial states and states.
		ts.getActions().forEach(inputsMap -> registersMaps.stream()
				.map(registersMap -> new Pair<>(inputsMap, registersMap))
				.peek(ts::addState)
				.filter(stateEntry -> !stateEntry.getSecond().containsValue(true))
				.forEach(ts::addInitialState));

		// Adding all the transitions.
		Set<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitions = ts.getActions().stream()
				.flatMap(action -> ts.getStates().stream()
						.map(state -> new TSTransition<>(state, action, new Pair<>(action, circuit.updateRegisters(state.getFirst(), state.getSecond())))))
//				.distinct() // for safety, maybe not needed
				.peek(ts::addTransition)
				.collect(Collectors.toSet());

		final Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> newReachableStates = reach(ts);
		ts.getStates().stream()
				.filter(Predicate.not(newReachableStates::contains))
				.peek(state -> transitions.stream()
						.filter(transition -> state.equals(transition.getFrom()) || state.equals(transition.getTo()))
						.distinct()
						.forEach(ts::removeTransition))
				.forEach(ts::removeState);

		// Adding all the atomic propositions.
		Stream.of(circuit.getInputPortNames(), circuit.getRegisterNames(), circuit.getOutputPortNames())
				.flatMap(Set::stream)
				.forEach(ts::addAtomicProposition);

		// Adding labels
		ts.getStates().forEach(state -> Stream.of(state.getFirst(), state.getSecond(), circuit.computeOutputs(state.getFirst(), state.getSecond()))
				.map(Map::entrySet)
				.flatMap(Set::stream)
				.filter(Map.Entry::getValue)
				.forEach(inputOrRegisterOrOutput -> ts.addToLabel(state, inputOrRegisterOrOutput.getKey())));

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

		/*
		  Adding all the actions.
		 */
		pg.getTransitions().stream()
				.filter(transition -> !transition.getAction().equals(""))
				.map(PGTransition::getAction)
				.forEach(ts::addAction);

		// Adding all the locations.
		Set<Map<String, Object>> evals = new HashSet<>();
		for (List<String> actions : pg.getInitalizations())
		{
//			Map<String, Object> eval = new HashMap<>();
//			for (String action : actions)
//				eval = ActionDef.effect(actionDefs, eval, action);
//			evals.add(eval);
			// TODO check, should work
			evals.add(actions.parallelStream()
					.reduce((Map<String, Object>) new HashMap<String, Object>(),
							(prevResult, element) -> ActionDef.effect(actionDefs, prevResult, element),
							(result1, result2) -> result2));
		}
		if (evals.isEmpty())
			evals.add(new HashMap<>());

		// Adding all the atomic propositions.
		pg.getInitialLocations()
				.forEach(initLoc ->
						evals.forEach(eval ->
						{
							ts.addInitialState(new Pair<>(initLoc, eval));
							eval.keySet().stream()
									.map(var -> var + " = " + eval.get(var))
									.forEach(ts::addAtomicProposition);
						}));

		// Adding all the transitions.
		Queue<Pair<L, Map<String, Object>>> states = new LinkedList<>(ts.getStates());
		while (!states.isEmpty())
		{
			Pair<L, Map<String, Object>> state = states.poll();
			pg.getTransitions().stream()
					.filter(transition -> state.getFirst().equals(transition.getFrom()) &&
					                      ConditionDef.evaluate(conditionDefs, state.getSecond(), transition.getCondition()))
					.forEach(transition ->
					{
						Map<String, Object> effect = ActionDef.effect(actionDefs, state.getSecond(), transition.getAction());
						if (effect != null)
						{
							Pair<L, Map<String, Object>> to = new Pair<>(transition.getTo(), effect);
							if (!ts.getStates().contains(to))
							{
								ts.addState(to);
								states.add(to);
							}
							if (ConditionDef.evaluate(conditionDefs, state.getSecond(), transition.getCondition()))
								ts.addTransition(new TSTransition<>(state, transition.getAction(), to));
						}
					});
		}

		new HashSet<>(ts.getStates()).stream()
				.filter(Predicate.not(reach(ts)::contains))
				.forEach(ts::removeState);

		// Adding all the labeling.
		ts.getStates()
				.forEach(state ->
				{
					if (state.getFirst() instanceof List<?>)
						//noinspection unchecked
						((List<L>) state.getFirst())
								.forEach(l ->
								{
									ts.addAtomicProposition(l.toString());
									ts.addToLabel(state, l.toString());
								});
					else
					{
						ts.addAtomicProposition(state.getFirst().toString());
						ts.addToLabel(state, state.getFirst().toString());
					}
					// TODO why pg.getTransitions()?
					pg.getTransitions().stream()
							.flatMap(transition -> state.getSecond().keySet().stream())
							.forEach(key ->
							{
								ts.addAtomicProposition(key + " = " + state.getSecond().get(key));
								ts.addToLabel(state, key + " = " + state.getSecond().get(key));
							});
				});

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
		return transitionSystemFromChannelSystem(cs, Collections.singleton(new ParserBasedActDef()), Collections.singleton(new ParserBasedCondDef()));
	}

	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
			ChannelSystem<L, A> cs,
			Set<ActionDef> actions,
			Set<ConditionDef> conditions)
	{
		ProgramGraph<List<L>, A> pg = new ProgramGraph<>();

		// first pg
		ProgramGraph<L, A> pg1 = cs.getProgramGraphs().get(0);
		for (L locij : pg1.getLocations())
		{
			// locations
			List<L> newLoc = new LinkedList<>();
			newLoc.add(locij);
			pg.addLocation(newLoc);

			// init
			if (pg1.getInitialLocations().contains(locij))
				pg.setInitial(newLoc, true);
		}

		// trans
		for (PGTransition<L, A> tran : pg1.getTransitions())
			pg.addTransition(new PGTransition<>(
					Arrays.asList(tran.getFrom()), tran.getCondition(), tran.getAction(), Arrays.asList(tran.getTo())));

		// initializations
		pg1.getInitalizations().forEach(pg::addInitalization);
//		for (List<String> inits : pg1.getInitalizations())
//			pg.addInitalization(inits);

		// rest pg-s
		for (int i = 1 /*why not 0??*/; i < cs.getProgramGraphs().size(); i++)
			pg = addProgramGraphs(pg, cs.getProgramGraphs().get(i));

		Set<ActionDef> actionDefs = new LinkedHashSet<>();
		actionDefs.add(new ParserBasedInterleavingActDef());
		actionDefs.add(new ParserBasedActDef());
		Set<ConditionDef> conditionDefs = new HashSet<>();
		conditionDefs.add(new ParserBasedCondDef());

		return transitionSystemFromProgramGraph(pg, actionDefs, conditionDefs);
//        throw new java.lang.UnsupportedOperationException();
	}

	private <L, A> ProgramGraph<List<L>, A> addProgramGraphs(ProgramGraph<List<L>, A> pgAll, ProgramGraph<L, A> pgi)
	{
		ProgramGraph<List<L>, A> pg = new ProgramGraph<>();
		// locations
//		Set<List<L>> locations = new HashSet<>(pgAll.getLocations());
//		for (List<L> locs : locations)
		for (List<L> locs : pgAll.getLocations())
		{
			for (L locij : pgi.getLocations())
			{
				List<L> newLoc = new ArrayList<>(locs);
				newLoc.add(locij);
				pg.addLocation(newLoc);

				// init
				if (pgi.getInitialLocations().contains(locij) && pgAll.getInitialLocations().contains(locs))
					pg.setInitial(newLoc, true);
			}
		}

		// trans
		ParserBasedInterleavingActDef parser = new ParserBasedInterleavingActDef();
//		Set<PGTransition<List<L>, A>> transitions = new HashSet<>(pgAll.getTransitions());
//		for (PGTransition<List<L>, A> pgTransition : transitions)
		for (PGTransition<List<L>, A> pgTransition : pgAll.getTransitions())
		{
			if (!parser.isOneSidedAction(pgTransition.getAction().toString()))
				for (L loc : pgi.getLocations())
				{
					List<L> from = new ArrayList<>(pgTransition.getFrom());
					from.add(loc);
					List<L> to = new ArrayList<>(pgTransition.getTo());
					to.add(loc);
					PGTransition<List<L>, A> newTran = new PGTransition<>(from, pgTransition.getCondition(), pgTransition.getAction(), to);
					pg.addTransition(newTran);
				}
		}

		pgi.getTransitions().stream()
				.filter(pgiTransition -> !parser.isOneSidedAction(pgiTransition.getAction().toString()))
				.forEach(pgiTransition -> pgAll.getLocations()
						.forEach(loc ->
						{
							List<L> from = new ArrayList<>(loc);
							from.add(pgiTransition.getFrom());
							List<L> to = new ArrayList<>(loc);
							to.add(pgiTransition.getTo());
							pg.addTransition(new PGTransition<>(from, pgiTransition.getCondition(), pgiTransition.getAction(), to));
						}));

//		transitions = new HashSet<>(pgAll.getTransitions());
//		transitions.
		pgAll.getTransitions()
				.forEach(pgTransition -> pgi.getTransitions()
						.forEach(pgiTransition ->
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
						}));

		// initializations
//		Set<List<String>> inits = new HashSet<>(pgAll.getInitalizations());
//		init.
		pgAll.getInitalizations()
				.forEach(pgInits -> pgi.getInitalizations()
						.forEach(pgiInits ->
						{
							List<String> init = new ArrayList<>(pgInits);
							init.addAll(pgiInits);
							pg.addInitalization(init);
						}));
		if (pgAll.getInitalizations().isEmpty())
			pgi.getInitalizations().forEach(pg::addInitalization);

		if (pgi.getInitalizations().isEmpty())
			pgAll.getInitalizations().forEach(pg::addInitalization);
		return pg;
	}

	private <A> A getHandShakeAction(A pgAction, A pgiAction, ParserBasedInterleavingActDef parser)
	{
		if (!(pgAction instanceof String &&
		      pgiAction instanceof String &&
		      parser.isOneSidedAction(pgAction.toString()) &&
		      parser.isOneSidedAction(pgiAction.toString())))
			return null;

		if (((String) pgAction).contains("?") && ((String) pgiAction).contains("!"))
		{
			String pgChannel = ((String) pgAction).substring(0, ((String) pgAction).indexOf("?"));
			String pgiChannel = ((String) pgiAction).substring(0, ((String) pgiAction).indexOf("!"));
			if (pgChannel.equals(pgiChannel))
				//noinspection unchecked
				return (A) String.format("%s|%s", pgAction, pgiAction);
		}

		if (((String) pgAction).contains("!") && ((String) pgiAction).contains("?"))
		{
			String pgChannel = ((String) pgAction).substring(0, ((String) pgAction).indexOf("!"));
			String pgiChannel = ((String) pgiAction).substring(0, ((String) pgiAction).indexOf("?"));
			if (pgChannel.equals(pgiChannel))
				//noinspection unchecked
				return (A) String.format("%s|%s", pgAction, pgiAction);
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
	 */
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela)
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

	private ProgramGraph<String, String> programGraphFromNanoPromela(NanoPromelaParser.StmtContext nanopromela)
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
				locsToTransitions.get(loc)
						.forEach(transition ->
						{
							if (!pg.getLocations().contains(transition.getTo()))
							{
								pg.addLocation(transition.getTo());
								locs.add(transition.getTo());
							}
							pg.addTransition(transition);
						});
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
		final TransitionSystem<Pair<Sts, Saut>, A, Saut> transitionSystem = new TransitionSystem<>();
		final Set<Saut> qs = aut.getTransitions().keySet();

		transitionSystem.addAllActions(ts.getActions()); // Actₓ=Act_TS
		transitionSystem.addAllAtomicPropositions(qs); // APₓ=Q
		ts.getStates()
				.forEach(s -> qs.stream()
						.map(q -> new Pair<>(s, q))
						.forEach(pair ->
						{
							transitionSystem.addState(pair); // Sₓ=S_TS×Q
							transitionSystem.addToLabel(pair, pair.getSecond()); // Lₓ(⟨s, q⟩)={q}
							if (ts.getInitialStates().contains(pair.getFirst())) // pair.getFirst() is s₀
								aut.getInitialStates() // Q₀
										.forEach(q_0 ->
										{
											if (aut.nextStates(q_0, ts.getLabel(pair.getFirst())).contains(pair.getSecond())) //  ∃q₀∈Q₀.q∈𝛿(q₀, L(s₀)), pair.getSecond() is q
												transitionSystem.addInitialState(pair); // ⟨s₀, q⟩
										}); // Iₓ = {⟨s₀, q⟩: s₀∈I_TS ∧ ∃q₀∈Q₀ . q∈𝛿(q₀, L(s₀))}
						}));

		// →ₓ
		ts.getTransitions()
				.forEach(transition ->
						qs.forEach(q -> aut.nextStates(q, ts.getLabel(transition.getTo()))
								.forEach(p -> transitionSystem.addTransition(new TSTransition<>(new Pair<>(transition.getFrom(), q), transition.getAction(), new Pair<>(transition.getTo(), p))))));

		transitionSystem.setName("TSₓ=TS_" + ts.getName() + "×A");
		return transitionSystem;
//		throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * inner DFS
	 *
	 * @param ts     The transition system.
	 * @param s      initial state.
	 * @param t      Set of visited states in the inner DFS.
	 * @param v      Stack for the inner DFS.
	 * @param <S>    Type of states in the transition system.
	 * @param <A>    Type of actions in the transition system.
	 * @param <Saut> Type of atomic propositions in the transition system.
	 * @return {@code true} if {@code s} belongs to cycle
	 */
	private <S, A, Saut> boolean cycleCheck(TransitionSystem<Pair<S, Saut>, A, Saut> ts,
	                                        Pair<S, Saut> s,
	                                        Set<Pair<S, Saut>> t,
	                                        Deque<Pair<S, Saut>> v)
	{
		boolean cycleFound = false; // no cycle found yet
		v.push(s); // push s on the stack
		do
		{
			final Set<Pair<S, Saut>> postSTag = post(ts, v.peek() /* take top element of V */);
			if (postSTag.contains(s))
				cycleFound = true; // if s∈Post(s'), a cycle is found
			else
			{
				final HashSet<Pair<S, Saut>> postSTagWithoutT = new HashSet<>(postSTag);
				postSTagWithoutT.removeAll(t);
				if (!postSTagWithoutT.isEmpty())
					v.push(postSTagWithoutT.stream().findFirst().get()); //push an unvisited successor of s'
				else
					v.pop(); // unsuccessful cycle search for s'
			}
		}
		while (!(v.isEmpty() || cycleFound));
		return cycleFound;
	}

	/**
	 * outer DFS
	 *
	 * @param ts     The transition system.
	 * @param aut    A Büchi automaton for the words that do not satisfy the property.
	 * @param s      initial state.
	 * @param r      Set of visited states in the outer DFS.
	 * @param u      Stack for the outer DFS.
	 * @param t      Set of visited states in the inner DFS.
	 * @param v      Stack for the inner DFS.
	 * @param <S>    Type of states in the transition system.
	 * @param <A>    Type of actions in the transition system.
	 * @param <Saut> Type of atomic propositions in the transition system.
	 * @return {@code true} if {@code s} belongs to cycle
	 */
	private <S, A, Saut> boolean reachableCycle(TransitionSystem<Pair<S, Saut>, A, Saut> ts,
	                                            Automaton<Saut, ?> aut,
	                                            Pair<S, Saut> s,
	                                            Set<Pair<S, Saut>> r,
	                                            Deque<Pair<S, Saut>> u,
	                                            Set<Pair<S, Saut>> t,
	                                            Deque<Pair<S, Saut>> v)
	{
		boolean cycleFound = false;
		u.push(s); // push s on the stack
		r.add(s);
		do
		{
			final Pair<S, Saut> sTag = u.peek();
			final Set<Pair<S, Saut>> postSTagWithoutR = post(ts, sTag);
			postSTagWithoutR.removeAll(r);
			if (!postSTagWithoutR.isEmpty())
			{
				final Pair<S, Saut> sTagTag = postSTagWithoutR.stream().findFirst().get();
				u.push(sTagTag); // push the unvisited successor of s'
				r.add(sTagTag); // and mark it reachable
			} else
			{
				u.pop(); // outer DFS finished for s'
				if (!aut.getAcceptingStates().contains(sTag.getSecond())) // s'⊭𝛷 TODO check (shouldn't because u.push(s) at the beginning)
					cycleFound = cycleCheck(ts, sTag, t, v); // proceed with the inner DFS in state s'
			}

		} while (!(u.isEmpty() || cycleFound)); // stop when stack for the outer DFS is empty or cycle found
		return cycleFound;
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
		final Set<Pair<S, Saut>> r = new HashSet<>(), t = new HashSet<>();
		final Deque<Pair<S, Saut>> u = new LinkedList<>(), v = new LinkedList<>();
		boolean cycleFound = false;

		final TransitionSystem<Pair<S, Saut>, A, Saut> ts_x = product(ts, aut);

		final HashSet<Pair<S, Saut>> initialsWithoutR = new HashSet<>(ts_x.getInitialStates());
		for (; !initialsWithoutR.isEmpty() && !cycleFound; initialsWithoutR.removeAll(r))
			cycleFound = reachableCycle(ts_x, aut, initialsWithoutR.stream().findFirst().get() /* explore the reachable */, r, u, t, v); // fragment with outer DFS

		if (!cycleFound)
			return new VerificationSucceeded<>(); // TS⊨"eventually forever/always 𝛷"≡◇□𝛷

		final VerificationFailed<S> failure = new VerificationFailed<>();

//		failure.setPrefix(v.stream()
//				.map(Pair::getFirst)
//				.collect(LinkedList::new,
//						LinkedList::addFirst,
//						(list1, list2) -> list1.addAll(0, list2)));

		final List<S> reverseListV = new LinkedList<>();
		v.descendingIterator().forEachRemaining(pair -> reverseListV.add(pair.getFirst()));
		failure.setCycle(reverseListV);

		final List<S> reverseListU = new LinkedList<>();
		u.descendingIterator().forEachRemaining(pair -> reverseListU.add(pair.getFirst()));
		failure.setPrefix(reverseListU);
		return failure; // stack contents yield a counterexample
//		throw new java.lang.UnsupportedOperationException();
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
		final Automaton<Pair<?, Integer>, L> automaton = new Automaton<>();
		final Set<Integer> colors = mulAut.getColors();

		if (colors.isEmpty()) // edge case
		{
			mulAut.getInitialStates()
					.forEach(state -> automaton.setInitial(new Pair<>(state, null)));

			mulAut.getTransitions()
					.forEach((source, setSetMap) ->
					{
						final Pair<?, Integer> sourcePair = new Pair<>(source, null);
						automaton.setAccepting(sourcePair);
						setSetMap.forEach((ls, states) ->
								states.forEach(destination ->
								{
									final Pair<?, Integer> destinationPair = new Pair<>(destination, null);
									automaton.addTransition(sourcePair, ls, destinationPair);
									automaton.setAccepting(destinationPair);
								}));
					});
		} else
		{
			final Integer[] colorsByOrder = colors.toArray(new Integer[0]);

			mulAut.getInitialStates()
					.forEach(state -> automaton.setInitial(new Pair<>(state, colorsByOrder[0])));

			mulAut.getAcceptingStates(colorsByOrder[0])
					.forEach(state -> automaton.setAccepting(new Pair<>(state, colorsByOrder[0])));

			for (int i = 0; i < colorsByOrder.length; i++)
			{
				final int finalI = i;
				mulAut.getTransitions()
						.forEach((source, lsStatesMap) ->
						{
							final boolean isSourceAcceptingState = mulAut.getAcceptingStates(colorsByOrder[finalI]).contains(source);
							lsStatesMap.forEach((ls, states) ->
									states.forEach((destination ->
											automaton.addTransition(new Pair<>(source, colorsByOrder[finalI]), ls, new Pair<>(destination, colorsByOrder[isSourceAcceptingState ? (finalI + 1) % colorsByOrder.length : finalI])))));
						});
			}
		}
		return automaton;
//		throw new java.lang.UnsupportedOperationException();
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
		MultiColorAutomaton<Set<LTL<L>>, L> automaton = new MultiColorAutomaton<>();
		Queue<LTL<L>> ltlExpressionsToAdd = new LinkedList<>();
		ltlExpressionsToAdd.add(ltl);
		Set<LTL<L>> ltlExpressions = new HashSet<>();

		while (!ltlExpressionsToAdd.isEmpty())
		{
			LTL<L> ltlSubExpression = ltlExpressionsToAdd.poll();
			if (!ltlExpressions.contains(ltlSubExpression))
				if (ltlSubExpression instanceof Not)
					ltlExpressionsToAdd.add(((Not<L>) ltlSubExpression).getInner());
				else
				{
					ltlExpressions.add(ltlSubExpression);
					if (ltlSubExpression instanceof And || ltlSubExpression instanceof Until)
					{
						ltlExpressionsToAdd.add((ltlSubExpression instanceof And) ? ((And<L>) ltlSubExpression).getLeft() : ((Until<L>) ltlSubExpression).getLeft());
						ltlExpressionsToAdd.add((ltlSubExpression instanceof And) ? ((And<L>) ltlSubExpression).getRight() : ((Until<L>) ltlSubExpression).getRight());
					} else if (ltlSubExpression instanceof Next)
						ltlExpressionsToAdd.add(((Next<L>) ltlSubExpression).getInner());
				}
		}

		Set<Until<L>> untilLtlExpressions = ltlExpressions.stream()
				.filter(ltlExpression -> ltlExpression instanceof Until)
				.map(ltlExpression -> (Until<L>) ltlExpression)
				.collect(Collectors.toSet());

		Set<Next<L>> nextLtlExpressions = ltlExpressions.stream()
				.filter(ltlExpression -> ltlExpression instanceof Next)
				.map(ltlExpression -> (Next<L>) ltlExpression)
				.collect(Collectors.toSet());

		int ltlSize = 1 << ltlExpressions.size();

		List<Set<LTL<L>>> ltlSubExpressions = new ArrayList<>(ltlSize);
		for (int m = 0; m < ltlSize; m++)
			ltlSubExpressions.add(new HashSet<>(ltlExpressions.size()));

		{
			int m, n, acc;
			Iterator<LTL<L>> ltlIterator = ltlExpressions.iterator();
			LTL<L> ltlExpression;
			boolean flag;
			for (m = 1; ltlIterator.hasNext(); m *= 2)
				for (n = 0, acc = 0, flag = true, ltlExpression = ltlIterator.next(); n < ltlSize; n++)
				{
					ltlSubExpressions.get(n).add(flag ? ltlExpression : not(ltlExpression));
					acc = (acc + 1) % m;
					flag = (acc == 0) != flag;
				}
		}

		List<Set<LTL<L>>> states = new LinkedList<>();
		for (Set<LTL<L>> ltlSubExpression : ltlSubExpressions)
		{
			Iterator<LTL<L>> ltlSubExpressionIterator = ltlSubExpression.iterator();
			boolean flag = !ltlSubExpression.contains(not(new TRUE<L>()));
			while (flag && ltlSubExpressionIterator.hasNext())
			{
				LTL<L> ltlExpression = ltlSubExpressionIterator.next();
				if (ltlExpression instanceof Until)
					flag = ltlSubExpression.contains(((Until<L>) ltlExpression).getRight()) || ltlSubExpression.contains(((Until<L>) ltlExpression).getLeft());
				else if (ltlExpression instanceof And)
					flag = ltlSubExpression.contains(((And<L>) ltlExpression).getLeft()) && ltlSubExpression.contains(((And<L>) ltlExpression).getRight());
				else if (ltlExpression instanceof Not)
				{
					LTL<L> innerItem = ((Not<L>) ltlExpression).getInner();
					if (innerItem instanceof Until)
						flag = !(ltlSubExpression.contains(((Until<L>) innerItem).getRight()));
					else if (innerItem instanceof And)
						flag = !(ltlSubExpression.contains(((And<L>) innerItem).getLeft()) && ltlSubExpression.contains(((And<L>) innerItem).getRight()));
				}
			}
			if (flag)
				states.add(ltlSubExpression);
		}

		states.forEach(state ->
		{
			automaton.addState(state);
			if (state.contains(ltl))
				automaton.setInitial(state);
		});

		int color = 0;
		for (Until<L> untilLtlExpression : untilLtlExpressions)
		{
			for (Set<LTL<L>> state : states)
				if (!state.contains(untilLtlExpression) || state.contains(untilLtlExpression.getRight()))
					automaton.setAccepting(state, color);
			color++;
		}

		states.forEach(sourceState ->
		{
			Set<L> actions = sourceState.stream()
					.filter(exp -> exp instanceof AP)
					.map(exp -> ((AP<L>) exp).getName())
					.collect(Collectors.toSet());
			sourceState.forEach(exp ->
					states.forEach(destinationState ->
					{
						if (nextLtlExpressions.stream()
								    .noneMatch(e -> sourceState.contains(e) != destinationState.contains(e.getInner())) &&
						    untilLtlExpressions.stream()
								    .noneMatch(e -> sourceState.contains(e) != (sourceState.contains(e.getRight()) ||
								                                                (sourceState.contains(e.getLeft()) && destinationState.contains(e)))))
							automaton.addTransition(sourceState, actions, destinationState);
					}));
		});
		if (automaton.getColors().isEmpty())
			states.forEach(state -> automaton.setAccepting(state, 0));
		return GNBA2NBA(automaton);
	}

	/**
	 * Verify that a system satisfies an LTL formula under fairness conditions.
	 *
	 * @param ts  Transition system
	 * @param fc  Fairness condition
	 * @param ltl An LTL formula
	 * @param <S> Type of states in the transition system
	 * @param <A> Type of actions in the transition system
	 * @param <P> Type of atomic propositions in the transition system
	 * @return a VerificationSucceeded object or a VerificationFailed object with a counterexample.
	 */
	public <S, A, P> VerificationResult<S> verifyFairLTLFormula(TransitionSystem<S, A, P> ts, FairnessCondition<A> fc, LTL<P> ltl)
	{
		TransitionSystem<Pair<S, A>, A, ExtendedAP> tsF = new TransitionSystem<>();
		LTL<ExtendedAP> newLTL = reconstructLTLWithExtendedAP(ltl); //Make ltl as extendedAP type
		tsF.addAllActions(ts.getActions());
		ts.getStates()
				.forEach(state ->
						ts.getActions().stream()
								.map(act -> new Pair<>(state, act))
								.forEach(newState ->
								{
									tsF.addState(newState);
									if (ts.getInitialStates().contains(state))
										tsF.addInitialState(newState);
								}));
		Set<ExtendedAP> extendedAP = ts.getAtomicPropositions().stream()
				.map(OriginalAP::new)
				.collect(Collectors.toSet());
		ts.getActions()
				.forEach(act ->
				{
					extendedAP.add(new TriggeredAP<>(act));
					extendedAP.add(new EnabledAP<>(act));
				});
		tsF.getStates().forEach(state ->
		{
			ts.getLabelingFunction().get(state.getFirst())
					.forEach(ap -> tsF.addToLabel(state, new OriginalAP<>(ap)));
			tsF.addToLabel(state, new TriggeredAP<>(state.getSecond()));
			ts.getActions().stream()
					.filter(act -> !post(ts, state.getFirst(), act).isEmpty())
					.forEach(act -> tsF.addToLabel(state, new EnabledAP<>(act)));
		});
		tsF.addAllAtomicPropositions(extendedAP);

		ts.getTransitions()
				.forEach(transition ->
						tsF.getStates().stream()
								.filter(s -> s.getFirst().equals(transition.getFrom()))
								.forEach(state -> tsF.addTransitionFrom(state).action(transition.getAction()).to(new Pair<>(transition.getTo(), transition.getAction()))));

		//TS is ready. now we will verify each fairness constraint
		VerificationResult<Pair<S, A>> fulfilled = null;
		for (Set<A> unconditionalConstraint : fc.getUnconditional())
		{
			for (A act : unconditionalConstraint)
			{
				ExtendedAP actAP = new TriggeredAP<>(act);
				AP<ExtendedAP> ap = new AP<>(actAP);
				fulfilled = checkConstraint(tsF, LTLUtil.implies(LTLUtil.eventuallyAlways(ap), newLTL));
				if (fulfilled instanceof VerificationSucceeded)
					break;
			}
			//if all action set is not fulfilled at all - build verificationFailed<S> and return it.
			if (fulfilled instanceof VerificationFailed)
				return buildVerificationFailedObject((VerificationFailed<Pair<S, A>>) fulfilled);
		}

		for (Set<A> strongConstraint : fc.getStrong())
		{
			for (A act : strongConstraint)
			{
				ExtendedAP triggered = new TriggeredAP<>(act);
				AP<ExtendedAP> triggeredAP = new AP<>(triggered);
				ExtendedAP enabled = new EnabledAP<>(act);
				AP<ExtendedAP> enabledAP = new AP<>(enabled);
				fulfilled = checkConstraint(tsF, LTLUtil.implies(LTLUtil.implies(LTLUtil.alwaysEventually(enabledAP), LTLUtil.alwaysEventually(triggeredAP)), newLTL));
				if (fulfilled instanceof VerificationSucceeded)
					break;
			}
			if (fulfilled instanceof VerificationFailed)
				return buildVerificationFailedObject((VerificationFailed<Pair<S, A>>) fulfilled);
		}

		for (Set<A> weakConstraint : fc.getWeak())
		{
			for (A act : weakConstraint)
			{
				ExtendedAP triggered = new TriggeredAP<>(act);
				AP<ExtendedAP> triggeredAP = new AP<>(triggered);
				ExtendedAP enabled = new EnabledAP<>(act);
				AP<ExtendedAP> enabledAP = new AP<>(enabled);
				fulfilled = checkConstraint(tsF, LTLUtil.implies(LTLUtil.implies(LTLUtil.eventuallyAlways(enabledAP), LTLUtil.alwaysEventually(triggeredAP)), newLTL));
				if (fulfilled instanceof VerificationSucceeded)
					break;
			}
			if (fulfilled instanceof VerificationFailed)
				return buildVerificationFailedObject((VerificationFailed<Pair<S, A>>) fulfilled);
		}

		return new VerificationSucceeded<>();
//		throw new java.lang.UnsupportedOperationException();
	}

	private <S, A> VerificationFailed<S> buildVerificationFailedObject(VerificationFailed<Pair<S, A>> res)
	{
		VerificationFailed<S> toReturn = new VerificationFailed<>();
		toReturn.setPrefix(res.getPrefix().stream()
				.map(Pair::getFirst)
				.collect(Collectors.toList()));
		toReturn.setCycle(res.getCycle().stream()
				.map(Pair::getFirst)
				.collect(Collectors.toList()));
		return toReturn;
	}

	private <A, S> VerificationResult<Pair<S, A>> checkConstraint(TransitionSystem<Pair<S, A>, A, ExtendedAP> tsF, LTL<ExtendedAP> ap)
	{
		LTL<ExtendedAP> badPrefLTL = not(ap);
		Automaton<?, ExtendedAP> automaton = LTL2NBA(badPrefLTL);
		return verifyAnOmegaRegularProperty(tsF, automaton);
	}


	/**
	 * This class implements more ltl operators based on the basic operators appears in LTL<T> class.
	 */
	private static class LTLUtil
	{
		private LTLUtil()
		{
		}

		public static <A> LTL<A> eventually(LTL<A> phi)
		{
			return until(true_(), phi);
		}

		public static <A> LTL<A> always(LTL<A> phi)
		{
			return not(eventually(not(phi)));
		}

		public static <A> LTL<A> alwaysEventually(LTL<A> phi)
		{
			return always(eventually(phi));
		}

		public static <A> LTL<A> eventuallyAlways(LTL<A> phi)
		{
			return eventually(always(phi));
		}

		public static <A> LTL<A> or(LTL<A> phi1, LTL<A> phi2)
		{
			return not(and(not(phi1), not(phi2)));
		}

		public static <A> LTL<A> implies(LTL<A> phi1, LTL<A> phi2)
		{
			return not(and(phi1, not(phi2)));
		}
	}

	private abstract static class ExtendedAP
	{
	}

	private static class OriginalAP<P> extends ExtendedAP
	{
		private final P ap;

		OriginalAP(P ap)
		{
			this.ap = ap;
		}

		public P getAp()
		{
			return ap;
		}
	}

	private static class TriggeredAP<A> extends ExtendedAP
	{
		private final A triggeredAct;

		TriggeredAP(A triggeredAct)
		{
			this.triggeredAct = triggeredAct;
		}

		public A getTriggeredAct()
		{
			return triggeredAct;
		}
	}

	private static class EnabledAP<A> extends ExtendedAP
	{
		private final A enabledAP;

		EnabledAP(A enabledAP)
		{
			this.enabledAP = enabledAP;
		}

		public A getEnabledAP()
		{
			return enabledAP;
		}
	}
}
