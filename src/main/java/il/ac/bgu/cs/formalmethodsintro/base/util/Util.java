package il.ac.bgu.cs.formalmethodsintro.base.util;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Utility methods for implementation.
 */
public class Util
{

	public static <T1, T2> Set<Pair<T1, T2>> getPairs(Set<T1> s1, Set<T2> s2)
	{
		return s1.stream()
				.flatMap(e1 -> s2.stream()
						.map(e2 -> new Pair<>(e1, e2)))
				.collect(Collectors.toSet());
	}

	public static <T> Set<Set<T>> powerSet(Set<T> aset)
	{
		List<T> orderedItems = new ArrayList<>(aset);

		return IntStream.range(0, 1 << aset.size() /*(int) Math.pow(2, aset.size())*/).parallel()
				.mapToObj(e -> IntStream.range(0, orderedItems.size())
						.filter(i -> (e & (0b1 << i)) != 0)
						.mapToObj(orderedItems::get)
						.collect(Collectors.toSet()))
				.collect(Collectors.toSet());
	}

	/**
	 * @param gnba
	 */
	public static <L> void printColoredAutomatonTransitions(MultiColorAutomaton<Set<LTL<L>>, L> gnba)
	{
		gnba.getTransitions().forEach((key1, value1) ->
				value1.forEach((key, value) ->
						value.forEach(s3 -> System.out.println(key1 + "----" + key + "---->" + s3))));
	}

	/**
	 * @param nba
	 */
	public static <S, L> void printAutomatonTransitions(Automaton<S, L> nba)
	{
		nba.getTransitions().forEach((key, value) ->
				value.forEach((key1, value1) ->
						value1.forEach(s3 -> System.out.println(key + "----" + key1 + "---->" + s3))));
	}

}
