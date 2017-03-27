package edu.ucla.cs.parse;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;
import edu.ucla.cs.utils.FileUtils;

public class PartialProgramAnalyzerTest {
	@Test
	public void testMultipleMethodsInASnippet() throws Exception {
		String sample = "/home/troy/research/BOA/Maple/test/edu/ucla/cs/parse/snippet_with_multiple_method.txt";
		String snippet = FileUtils.readFileToString(sample);
		PartialProgramAnalyzer analyzer = new PartialProgramAnalyzer(snippet);
		HashSet<String> apis = new HashSet<String>();
		apis.add("next");
		ArrayList<ArrayList<APISeqItem>> seqs = new ArrayList<ArrayList<APISeqItem>>();
		ArrayList<APISeqItem> seq = new ArrayList<APISeqItem>();
		seq.add(ControlConstruct.IF);
		seq.add(new APICall("new NoSuchElementException", "!hasNext()"));
		seq.add(ControlConstruct.END_BLOCK);
		seq.add(new APICall("next", "true && !(!hasNext())"));
		seqs.add(seq);
		assertEquals(seqs, analyzer.retrieveAPICallSequences(apis));
	}
}
