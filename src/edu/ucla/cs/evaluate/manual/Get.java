package edu.ucla.cs.evaluate.manual;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.main.AnomalyDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class Get {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(ControlConstruct.IF);
		pattern1.add(new APICall("get", "rcv.containsKey(arg0,)"));
		pattern1.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(new APICall("get", "true"));
		pattern2.add(ControlConstruct.IF);
		pattern2.add(ControlConstruct.END_BLOCK);
		
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern1);
		patterns.add(pattern2);
		
		HashSet<String> types = new HashSet<String>();
		types.add("HashMap");
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> apis = new HashSet<String>();
		apis.add("get");
		queries.add(apis);
		
		AnomalyDetection detect = new AnomalyDetection(types, queries, patterns);
		detect.run();
	}
}
