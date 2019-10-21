package edu.ucla.cs.evaluate.top5;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.check.APIMisuseDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class HashMapGet {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(new APICall("get", "true", 1));
		pattern1.add(ControlConstruct.IF);
		pattern1.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern2 = new ArrayList<APISeqItem>();
		pattern2.add(new APICall("get", "rcv.containsKey(arg0,)", 1));
		pattern2.add(ControlConstruct.IF);
		pattern2.add(ControlConstruct.END_BLOCK);
		
		ArrayList<APISeqItem> pattern3 = new ArrayList<APISeqItem>();
		pattern3.add(ControlConstruct.IF);
		pattern3.add(new APICall("get", "rcv.containsKey(arg0,)", 1));
		pattern3.add(ControlConstruct.END_BLOCK);
		
		HashSet<ArrayList<APISeqItem>> patterns1 = new HashSet<ArrayList<APISeqItem>>();
		patterns1.add(pattern1);
		patterns1.add(pattern2);
		patterns1.add(pattern3);
		
		ArrayList<APISeqItem> pattern4 = new ArrayList<APISeqItem>();
		pattern4.add(new APICall("get", "rcv != null", 1));
		pattern4.add(ControlConstruct.IF);
		pattern4.add(ControlConstruct.END_BLOCK);
		
		HashSet<ArrayList<APISeqItem>> patterns2 = new HashSet<ArrayList<APISeqItem>>();
		patterns2.add(pattern4);
		
		ArrayList<APISeqItem> pattern5 = new ArrayList<APISeqItem>();
		pattern5.add(ControlConstruct.IF);
		pattern5.add(new APICall("get", "rcv != null", 1));
		pattern5.add(ControlConstruct.END_BLOCK);
		HashSet<ArrayList<APISeqItem>> patterns3 = new HashSet<ArrayList<APISeqItem>>();
		patterns3.add(pattern5);
		
		HashSet<HashSet<ArrayList<APISeqItem>>> pset = new HashSet<HashSet<ArrayList<APISeqItem>>>();
		pset.add(patterns1);
		pset.add(patterns2);
		pset.add(patterns3);
		
		HashSet<String> types = new HashSet<String>();
		types.add("HashMap");
		HashSet<ArrayList<String>> queries = new HashSet<ArrayList<String>>();
		ArrayList<String> apis = new ArrayList<String>();
		apis.add("get(1)");
		queries.add(apis);
		
		APIMisuseDetection detect = new APIMisuseDetection(types, queries, patterns1);
		detect.run2(pset);
	}
}
