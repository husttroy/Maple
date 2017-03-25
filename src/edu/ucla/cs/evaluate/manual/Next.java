package edu.ucla.cs.evaluate.manual;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.main.AnomalyDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class Next {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(ControlConstruct.IF);
		pattern1.add(new APICall("next", "rcv.hasNext()"));
		pattern1.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(ControlConstruct.LOOP);
		pattern2.add(new APICall("next", "rcv.hasNext()"));
		pattern2.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern3 = new ArrayList<APISeqItem>();
		pattern3.add(new APICall("add", "true"));
		pattern3.add(new APICall("next", "true"));
		
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern1);
		patterns.add(pattern2);
		patterns.add(pattern3);
		
		HashSet<String> types = new HashSet<String>();
		types.add("Iterator");
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> apis = new HashSet<String>();
		apis.add("next");
		queries.add(apis);
		
		AnomalyDetection detect = new AnomalyDetection(types, queries, patterns);
		detect.run();
	}
}
