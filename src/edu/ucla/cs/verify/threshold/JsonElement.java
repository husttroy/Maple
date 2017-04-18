package edu.ucla.cs.verify.threshold;

import java.util.ArrayList;

import edu.ucla.cs.mine.PreconditionVerifier;
import edu.ucla.cs.utils.FileUtils;

public class JsonElement {
	public static void main(String[] args) {
		String raw_output = "/home/troy/research/BOA/Maple/example/JsonElement.getAsString/large-sequence.txt";
		String seq_output = "/home/troy/research/BOA/Maple/example/JsonElement.getAsString/large-output.txt";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("getAsString(0)");
		int size = FileUtils.countLines(seq_output);
				
		// verify precondition
		PreconditionVerifier pv2 = new PreconditionVerifier(raw_output, seq_output, pattern);
		int count = pv2.verify("getAsString(0)", "!rcv.isJsonNull() || rcv.isJsonPrimitive()");
		double r2 = ((double) count) / size;
		System.out.println("precondition threshold: " + r2);		
	}
}
