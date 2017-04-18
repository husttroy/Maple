package edu.ucla.cs.verify.threshold;

import java.util.ArrayList;

import edu.ucla.cs.mine.PreconditionVerifier;
import edu.ucla.cs.mine.SequencePatternVerifier;
import edu.ucla.cs.utils.FileUtils;

public class SortedMap {
	public static void main(String[] args) {
		String raw_output = "/home/troy/research/BOA/Maple/example/SortedMap.firstKey/large-sequence-filter-tests.txt";
		String seq_output = "/home/troy/research/BOA/Maple/example/SortedMap.firstKey/large-output-filter-tests.txt";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("firstKey(0)");
		int size = FileUtils.countLines(seq_output);
				
		// verify sequence
		pattern.add(0, "put(2)");
		SequencePatternVerifier pv = new SequencePatternVerifier(pattern);
		pv.verify(seq_output);
		double r1 = ((double) pv.support.size()) / size;
		System.out.println("sequence threshold: " + r1);
		pattern.remove(0);
		 
		// verify precondition
		PreconditionVerifier pv2 = new PreconditionVerifier(raw_output, seq_output, pattern);
		int count = pv2.verify("firstKey(0)", "!rcv.isEmpty() || rcv.size() > 0");
		double r2 = ((double) count) / size;
		System.out.println("precondition threshold: " + r2);		
	}
}
