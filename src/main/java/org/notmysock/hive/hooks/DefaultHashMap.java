package org.notmysock.hive.hooks;

import java.util.HashMap;

public abstract class DefaultHashMap<K,V> extends HashMap<K,V> {
    public V getDefault(K key) {
        if (containsKey(key)) {
            return get(key);
        }
        V val = defaultValue(key);
        if (val != null) {
        	put(key, val);
        }
        return val;
    }
    public abstract V defaultValue(K key);
}
