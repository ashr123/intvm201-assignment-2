package il.ac.bgu.cs.formalmethodsintro.base.verification;

import java.util.List;

public class VerificationFailed<S> implements VerificationResult<S>
{
	List<S> prefix;
	List<S> cycle;

	public List<S> getPrefix()
	{
		return prefix;
	}

	public void setPrefix(List<S> prefix)
	{
		this.prefix = prefix;
	}

	public List<S> getCycle()
	{
		return cycle;
	}

	public void setCycle(List<S> cycle)
	{
		this.cycle = cycle;
	}

	@Override
	public String toString()
	{
		StringBuilder str = new StringBuilder("\tPrefix:\n");

		for (S s : prefix)
			str.append("\t\t").append(s).append("\n");

		str.append("\tCycle:\n");

		for (S s : cycle)
			str.append("\t\t").append(s).append("\n");

		return str.toString();
	}

}
