package il.ac.bgu.cs.formalmethodsintro.base.nanopromela;

import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;

public class NanoPromelaFileReader
{

	public static StmtContext parseNanoPromelaStream(InputStream in) throws IOException
	{

		return (StmtContext) new NanoPromelaParser(new CommonTokenStream(new NanoPromelaLexer(new ANTLRInputStream(in)))).stmt().getRuleContext();
	}

	public static StmtContext pareseNanoPromelaFile(String filename) throws IOException
	{

		return (StmtContext) new NanoPromelaParser(new CommonTokenStream(new NanoPromelaLexer(new ANTLRFileStream(filename)))).stmt().getRuleContext();
	}

	public static StmtContext pareseNanoPromelaString(String nanopromela)
	{

		return new NanoPromelaParser(new CommonTokenStream(new NanoPromelaLexer(new ANTLRInputStream(nanopromela)))).stmt();
	}

}
