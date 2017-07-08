package edu.ucla.cs.evaluate.manual;

import java.util.ArrayList;
import java.util.HashSet;

import edu.ucla.cs.main.AnomalyDetection;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;

public class JsonElement {
	public static void main(String[] args) {
		ArrayList<APISeqItem> pattern1 = new ArrayList<APISeqItem>();
		pattern1.add(new APICall("getAsString", "!rcv.isJsonNull() || rcv.isJsonPrimitive()", 0));
		
		HashSet<ArrayList<APISeqItem>> patterns = new HashSet<ArrayList<APISeqItem>>();
		patterns.add(pattern1);
		
		HashSet<String> types = new HashSet<String>();
		types.add("JsonElement");
		HashSet<ArrayList<String>> queries = new HashSet<ArrayList<String>>();
		ArrayList<String> apis = new ArrayList<String>();
		apis.add("getAsString(0)");
		queries.add(apis);
		
		AnomalyDetection detect = new AnomalyDetection(types, queries, patterns);
		detect.run();
	}
}