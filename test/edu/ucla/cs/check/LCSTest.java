package edu.ucla.cs.check;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class LCSTest {
	@Test
	public void testSimple() {
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
}
