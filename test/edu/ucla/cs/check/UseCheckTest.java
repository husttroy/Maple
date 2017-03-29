package edu.ucla.cs.check;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;
import edu.ucla.cs.model.Violation;

public class UseCheckTest {
	@Test
	public void testLCS() {
		APICall call1 = new APICall("createNewFile", "");
		APICall call2 = new APICall("new File", "");
		APICall call3 = new APICall("exists", "");
		APICall call4 = new APICall("foo", "");
		APICall call5 = new APICall("bar", "");
		
		ArrayList<APISeqItem> pattern = new ArrayList<APISeqItem>();
		pattern.add(ControlConstruct.IF);
		pattern.add(call1);
		pattern.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> seq = new ArrayList<APISeqItem>();
		assertEquals(0, new UseChecker().LCS(pattern, seq).size());
		
		seq.add(ControlConstruct.IF);
		assertEquals(1, new UseChecker().LCS(pattern, seq).size());
		
		seq.add(ControlConstruct.IF);
		assertEquals(1, new UseChecker().LCS(pattern, seq).size());
		

		seq.add(call2);
		seq.add(call3);
		assertEquals(1, new UseChecker().LCS(pattern, seq).size());
		
		seq.add(ControlConstruct.END_BLOCK);
		assertEquals(2, new UseChecker().LCS(pattern, seq).size());
	
		seq.add(call4);
		seq.add(call1);
		seq.add(call5);
		assertEquals(2, new UseChecker().LCS(pattern, seq).size());
		
		seq.add(ControlConstruct.END_BLOCK);
		assertEquals(3, new UseChecker().LCS(pattern, seq).size());
	}
	
	@Test
	public void testSameSequenceButDifferentPrecondition() {
		APICall call1 = new APICall("createNewFile", "true", "f", new ArrayList<String>());
		APICall call2 = new APICall("createNewFile", " flag && !f.exists()", "f", new ArrayList<String>());
		APICall call3 = new APICall("createNewFile", "!rcv.exists()");
		
		ArrayList<APISeqItem> seq1 = new ArrayList<APISeqItem>();
		seq1.add(ControlConstruct.IF);
		seq1.add(call1);
		seq1.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> seq2 = new ArrayList<APISeqItem>();
		seq2.add(ControlConstruct.IF);
		seq2.add(call2);
		seq2.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern = new ArrayList<APISeqItem>();
		pattern.add(ControlConstruct.IF);
		pattern.add(call3);
		pattern.add(ControlConstruct.END_BLOCK);
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern);
		
		UseChecker check = new UseChecker();
		ArrayList<Violation> vios1 = check.validate(patterns, seq1);
		assertEquals(1, vios1.size());
		
		ArrayList<Violation> vios2 = check.validate(patterns, seq2);
		assertEquals(0, vios2.size());
	}
}
