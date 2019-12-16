package il.ac.bgu.cs.formalmethodsintro.base;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only.<br>
 * More about facade: <a href="http://www.vincehuston.org/dp/facade.html">http://www.vincehuston.org/dp/facade.html</a>.
 */
public class FvmFacade
{

	private static FvmFacade INSTANCE = null;

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
		if (ts.getInitialStates().size() > 1)
			return false;
		for (S state : ts.getStates())
			for (A action : ts.getActions())
				if (post(ts, state, action).size() > 1)
					return false;
		return true;
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
//		if (ts.getInitialStates().size() > 1)
//			return false;
//		Set<Set<P>> LStateTag = new HashSet<Set<P>>();
//		for (S state : ts.getStates())
//		{
//			post(ts, state).parallelStream()
//					.map(ts::getLabel)
//					.forEach(LStateTag::add);
//			if (post(ts, state).size() != LStateTag.size())
//				return false;
//			LStateTag.clear();
//		}
//		return true;
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
//		throw new java.lang.UnsupportedOperationException();
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
		final AlternatingSequence<A, S> eNext = e.tail();
		if (eNext.isEmpty())
			return false;
		final AlternatingSequence<S, A> eNext2 = eNext.tail();
		if (eNext2.isEmpty())
			return false;
		if (ts.getTransitions().contains(new TSTransition<>(e.head(), eNext.head(), eNext2.head())))
			return isExecutionFragment(ts, eNext2);
		return false;
//		throw new java.lang.UnsupportedOperationException();
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
		return ts.getInitialStates().contains(e.head());
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
//		throw new java.lang.UnsupportedOperationException();
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
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
	                                                                      TransitionSystem<S2, A, P> ts2)
	{
		return interleave(ts1, ts2, Collections.emptySet());
//		throw new java.lang.UnsupportedOperationException();
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
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
	                                                                      TransitionSystem<S2, A, P> ts2,
	                                                                      Set<A> handShakingActions)
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
							final Consumer<P> pConsumer = label -> ts.addToLabel(pair, label);
							ts1.getLabel(pair.getFirst()).forEach(pConsumer);
							ts2.getLabel(pair.getSecond()).forEach(pConsumer); // S₁×S₂, AP₁∪AP₂, L(⟨s₁, s₂⟩)=L₁(s₁)∪L₂(s₂)
						}));

		ts.addAllActions(ts1.getActions());
		ts.addAllActions(ts2.getActions()); // Act₁∪Act₂

		/*→*/
//		for (TSTransition<S1, A> transition : ts1.getTransitions()) // example for TS₁
//		{
//			Set<Pair<S1, S2>>
//					fromPairs = ts.getStates().stream()
//					.filter(pair -> pair.getFirst().equals(transition.getFrom()))
//					.collect(Collectors.toSet()),
//					toPairs = ts.getStates().stream()
//							.filter(pair -> pair.getFirst().equals(transition.getTo()))
//							.collect(Collectors.toSet());
//			for (Pair<S1, S2> fromPair : fromPairs)
//				for (Pair<S1, S2> toPair : toPairs)
//					if (fromPair.getSecond().equals(toPair.getSecond()))
//						ts.addTransition(new TSTransition<>(fromPair, transition.getAction(), toPair));
//		}
		handShakingActions.forEach(action -> ts1.getTransitions().stream()
				.filter(transitionTS1 -> transitionTS1.getAction().equals(action))
				.forEach(transitionTS1 -> ts2.getTransitions().stream()
						.filter(transitionTS2 -> transitionTS2.getAction().equals(action) &&
								transitionTS2.getAction().equals(transitionTS1.getAction()))
						.forEach(transitionTS2 -> ts.getStates().stream()
								.filter(fromPair -> fromPair.getFirst().equals(transitionTS1.getFrom()) &&
										fromPair.getSecond().equals(transitionTS2.getFrom()))
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

//		ts1.getInitialStates()
//				.forEach(s1 -> ts2.getInitialStates().stream()
//						.map(s2 -> new Pair<>(s1, s2))
//						.forEach(ts::addInitialState)); // I₁×I₂
//
//		ts1.getAtomicPropositions().forEach(ts::addAtomicProposition);
//		ts2.getAtomicPropositions().forEach(ts::addAtomicProposition);

		ts.setName(ts1.getName() + (handShakingActions.isEmpty() ? '⫼' : "⫼_H") + ts2.getName());
//		ts.setName(ts1.getName() + "|||" + ts2.getName());

		return ts;
//		throw new java.lang.UnsupportedOperationException();
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

		//throw new java.lang.UnsupportedOperationException();
	}

	/**
	 * Creates a {@link TransitionSystem} representing the passed circuit.
	 *
	 * @param c The circuit to translate into a {@link TransitionSystem}.
	 * @return A {@link TransitionSystem} representing {@code c}.
	 */
	public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
			Circuit c)
	{
		TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = new TransitionSystem<>();
		Set<Map<String, Boolean>> inputs = new HashSet<>();
		ArrayList<String> inputNames = new ArrayList<>(c.getInputPortNames());
		Set<Map<String, Boolean>> registers = new HashSet<>();
		ArrayList<String> registerNames = new ArrayList<>(c.getRegisterNames());

		c.getInputPortNames()
				.forEach(ts::addAtomicProposition);
		c.getRegisterNames()
				.forEach(ts::addAtomicProposition);

		createBooleanValues(inputs, new HashMap<>(), inputNames, 0);
		createBooleanValues(registers, new HashMap<>(), registerNames, 0);
		addLabelApStates(ts, inputs, registers, c);
		addTransitions(ts,inputs, c);


		Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> reach = reach(ts);
		HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>> statesToRemove = new HashSet<>();
		HashSet<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transitionsToRemove = new HashSet<>();

		ts.getStates()
				.stream()
					.filter(state -> !reach.contains(state))
						.forEach(statesToRemove::add);
		statesToRemove
				.forEach(state -> ts.getTransitions().stream()
						.filter(transition -> transition.getFrom().equals(state) || transition.getTo().equals(state))
						.forEach(transitionsToRemove::add));
		transitionsToRemove
				.forEach(ts::removeTransition);
		statesToRemove
				.forEach(state -> {ts.getLabel(state).removeAll(ts.getLabel(state));
									ts.removeState(state);});

		/*
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> state1 : ts.getStates()) {
			if (!reach.contains(state1)) {
				statesToRemove.add(state1);
			}
		}
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> state1 : statesToRemove) {
			for (TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> tran: ts.getTransitions()) {
				if (tran.getFrom().equals(state1) || tran.getTo().equals(state1))
					transitionsToRemove.add(tran);
			}
		}
		for (TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> tran: transitionsToRemove)
			ts.removeTransition(tran);
		for (Pair<Map<String, Boolean>, Map<String, Boolean>> state1 : statesToRemove) {
			ts.getLabel(state1).removeAll(ts.getLabel(state1));
			ts.removeState(state1);
		}*/

		return ts;

		//throw new java.lang.UnsupportedOperationException();
	}

	/***
	 * Creates all the possible boolean input variables into dest.
	 *
	 * @param dest           The destination of the possible input.
	 * @param tempStorageVar A helper storage variable for the
	 * @param inputNames     Names of the inputs.
	 * @param index          Represents the index of the input.
	 */
	private void createBooleanValues(Set<Map<String, Boolean>> dest, Map<String, Boolean> tempStorageVar, ArrayList<String> inputNames, int index){
		if (index == inputNames.size())
			dest.add(tempStorageVar);
		HashMap<String,Boolean> inputTrue = new HashMap<>(tempStorageVar);
		HashMap<String,Boolean> inputFalse = new HashMap<>(tempStorageVar);
		inputTrue.put(inputNames.get(index), true);
		inputFalse.put(inputNames.get(index), false);
		createBooleanValues(dest,inputTrue,inputNames,index + 1);
		createBooleanValues(dest,inputFalse,inputNames,index + 1);
	}

	/***
	 * Adds the labels,atomic-propositions and states of {@link Circuit} to the {@link TransitionSystem}.
	 * @param ts        The {@link TransitionSystem} we build from the given {@link Circuit}.
	 * @param inputs    The given {@link Circuit} inputs.
	 * @param registers The given {@link Circuit} registers.
	 * @param circuit   The given {@link Circuit}.
	 */
	private void addLabelApStates(TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts, Set<Map<String, Boolean>> inputs, Set<Map<String, Boolean>> registers, Circuit circuit) {
		for (Map<String, Boolean> input: inputs) {
			ts.addAction(input);
			for (Map<String, Boolean> register : registers) {
				Pair<Map<String, Boolean>, Map<String, Boolean>> state = new Pair<>(input, register);
				ts.addState(state);

				input.keySet()
						.stream()
							.filter(str -> input.get(str))
								.forEach(str -> ts.addToLabel(state, str));

				AtomicBoolean init = new AtomicBoolean(false);

				register.keySet()
						.stream()
							.filter(str -> register.get(str))
								.forEach(str -> {ts.addToLabel(state, str);
									init.set(true);});

				Map<String, Boolean> outputs = circuit.computeOutputs(input, register);

				outputs.keySet()
						.forEach(str -> {ts.addAtomicProposition(str);
											if(outputs.get(str))
												ts.addToLabel(state, str);});

				if (!init.get())
					ts.addInitialState(state);
				ts.removeInitialState(state);
			}
		}
	}

	/***
	 * Adds the transitions of {@link Circuit} to the {@link TransitionSystem}.
	 *
	 * @param ts      The {@link TransitionSystem} we build from the given {@link Circuit}.
	 * @param inputs  The given {@link Circuit} inputs.
	 * @param circuit The given {@link Circuit}.
	 */
	private void addTransitions(TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts, Set<Map<String, Boolean>> inputs, Circuit circuit) {
		ts.getStates()
				.forEach(state -> {Map<String, Boolean> nextRegs = circuit.updateRegisters(state.getFirst(), state.getSecond());
									inputs.forEach(input -> ts.getStates()
											.stream()
												.filter(newState -> newState.getFirst().equals(input) && newState.getSecond().equals(nextRegs))
													.forEach(newState -> ts.addTransition(new TSTransition<>(state, input, newState))));});
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
		throw new java.lang.UnsupportedOperationException();
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
		throw new java.lang.UnsupportedOperationException();
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
		throw new java.lang.UnsupportedOperationException();
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
		throw new java.lang.UnsupportedOperationException();
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
		throw new java.lang.UnsupportedOperationException();
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
