package edu.ucla.cs.process;

import java.util.HashMap;

import edu.ucla.cs.model.Method;
import edu.ucla.cs.model.Class;

public class TypeProcessor extends ProcessStrategy{

	@Override
	public void process(String line) {
		if(line.startsWith("fields")) {
			Class c = getClassInstance(line);
			buildTypeMap(c.fields, line); 
		} else if(line.startsWith("locals")){
			Method m = getMethodInstance(line);
			buildTypeMap(m.locals, line);
		}
	}
	
	protected void buildTypeMap(HashMap<String, String> map, String line){
		String s = line.substring(line.indexOf("] =")).trim();
		String[] ss = s.split("\\|");
		// skip the first element because it is empty string
		for(int i = 1; i < ss.length; i++){
			String name = ss[i].split(":")[0];
			String type = ss[i].split(":")[1];
			map.put(name, type);
		}
	}
	
}
