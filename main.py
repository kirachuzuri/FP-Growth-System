import itertools
from tkinter import Tk, Label, Entry, Button, Radiobutton, StringVar, messagebox, scrolledtext, Frame, END
import os
import sys

current_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(current_dir)

# 建立FP-Tree的節點結構
class TreeNode:
    def __init__(self, name_value, num_occur, parent_node):
        self.name = name_value
        self.count = num_occur
        self.node_link = None
        self.parent = parent_node
        self.children = {}
    def inc(self, num_occur):
        self.count += num_occur

# 第一次掃描檔案，格式以看到冒號後開始、看到逗號為下一筆
def first_scan(file_path, min_support):
    item_counts = {}
    dataset = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            for line in f:
                if not line.strip(): continue
                parts = line.strip().split(':')
                if len(parts) < 2: continue
                items = parts[1].split(',')
                dataset.append(items)
                
                for item in items:
                    item_counts[item] = item_counts.get(item, 0) + 1
    except FileNotFoundError:
        return None, None
    # 統計所有單一物品的出現次數，並過濾掉未達min_support的物品，最後建立一個依出現次數降序排列的標頭表
    frequent_items = {k: v for k, v in item_counts.items() if v >= min_support}
    sorted_items = sorted(frequent_items.items(), key=lambda p: p[1], reverse=True)
    header_table = {item[0]: [item[1], None] for item in sorted_items}
    return dataset, header_table

# 第二次掃描資料，建立與挖掘 FP-Tree
def update_tree(items, in_tree, header_table, count):
    # 如果品項已經是當前節點的子節點，則直接增加其計數
    if items[0] in in_tree.children:
        in_tree.children[items[0]].inc(count)
    else:
        # 如果不存在，則建立新節點並加入子節點字典
        new_node = TreeNode(items[0], count, in_tree)
        in_tree.children[items[0]] = new_node

        # 更新頭指標表中的節點鏈結
        if header_table[items[0]][1] is None:
            # 如果目前鏈結為空，將新節點設為該品項的第一個節點
            header_table[items[0]][1] = new_node
        else:
            # 如果已有節點，則走訪至鏈結串列的末端，並將新節點接在後面
            current_node = header_table[items[0]][1]
            while current_node.node_link is not None:
                current_node = current_node.node_link
            current_node.node_link = new_node
        
    # 如果品項列表中還有其他品項，遞迴呼叫以處理下一個品項
    if len(items) > 1:
        update_tree(items[1:], in_tree.children[items[0]], header_table, count)

def build_fp_tree(dataset, header_table):
    # 初始化樹的根節點
    root = TreeNode('Null Set', 1, None)
    # 遍歷每筆交易紀錄
    for transaction in dataset:
        local_data = {}
        # 僅保留存在於頭指標表中的頻繁品項，並記錄其支援度計數
        for item in transaction:
            if item in header_table:
                local_data[item] = header_table[item][0]
        
        # 如果交易中包含頻繁品項，依據支援度計數由大到小排序，將排序後的品項列表插入
        if len(local_data) > 0:
            ordered_items = [v[0] for v in sorted(local_data.items(), key=lambda p: (p[1], p[0]), reverse=True)]
            update_tree(ordered_items, root, header_table, 1)
    return root

def find_prefix_path(base_pat, tree_node):
    cond_patterns = {}
    # 沿著節點鏈結走訪所有同名節點
    while tree_node is not None:
        prefix_path = []
        parent = tree_node.parent
        # 向上追溯至根節點，收集路徑上的所有祖先節點
        while parent.name != 'Null Set':
            prefix_path.append(parent.name)
            parent = parent.parent
        if len(prefix_path) > 0:
            cond_patterns[tuple(prefix_path)] = tree_node.count
        tree_node = tree_node.node_link
    return cond_patterns

def mine_fp_tree(header_table, min_support, prefix, frequent_itemset_list):
    # 將頭指標表中的品項依照支援度計數從小到大排序，由下往上挖掘
    sorted_items = [v[0] for v in sorted(header_table.items(), key=lambda p: (p[1][0], p[0]))]
    
    # 遍歷每一個品項作為基底
    for base_pat in sorted_items:
        new_frequent_set = prefix.copy()
        new_frequent_set.add(base_pat)
        frequent_itemset_list.append((new_frequent_set, header_table[base_pat][0]))
        
        cond_pattern_bases = find_prefix_path(base_pat, header_table[base_pat][1])

        cond_header_table = {}
        for path, count in cond_pattern_bases.items():
            for item in path:
                cond_header_table[item] = cond_header_table.get(item, 0) + count
                
        cond_header_table = {k: [v, None] for k, v in cond_header_table.items() if v >= min_support}
        
        if len(cond_header_table) > 0:
            cond_root = TreeNode('Null Set', 1, None)
            for path, count in cond_pattern_bases.items():
                local_data = [item for item in path if item in cond_header_table]
                if len(local_data) > 0:
                    local_data.sort(key=lambda x: (cond_header_table[x][0], x), reverse=True)
                    update_tree(local_data, cond_root, cond_header_table, count)
            
            mine_fp_tree(cond_header_table, min_support, new_frequent_set, frequent_itemset_list)

# 計算關聯規則
def generate_rules(frequent_itemsets, min_confidence):
    rules = []
    itemset_dict = {frozenset(itemset): support for itemset, support in frequent_itemsets}
    
    for itemset, support in frequent_itemsets:
        if len(itemset) < 2:
            continue  # 至少要2個物品
            
        # 找出該頻繁項集的所有子集
        for i in range(1, len(itemset)):
            for antecedent in itertools.combinations(itemset, i):
                antecedent_set = frozenset(antecedent)
                consequent_set = frozenset(itemset - antecedent_set)
                # 計算信賴度: supp(A ∪ B) / supp(A)
                denom = itemset_dict.get(antecedent_set)
                if denom:
                    confidence = support / denom
                    if confidence >= min_confidence:
                        rules.append((list(antecedent_set), list(consequent_set), confidence, support))
    return rules

# Tkinter GUI 介面
class FPGrowthGUI:
    def __init__(self, window):
        self.window = window
        self.window.title("Data Mining 期末作業 FP-Tree")
        self.window.geometry("650x600")
        
        # 預設系統參數
        self.file_path = "t2.txt"  # 取得資料
        self.current_min_supp = 60  # 預設最小支持度次數
        self.current_min_conf = 0.5 # 預設最小信賴度比例
        self.current_frequent_itemsets = [] # 暫存頻繁項集
        self.current_rules = []             # 暫存關聯規則
        
        # 1. 說明標籤
        Label(window, text="FP-Tree 關聯規則查詢系統", font=("Arial", 16, "bold")).pack(pady=10)
        
        # 2. 單選按鈕：選擇要輸入什麼 
        Label(window, text="選擇查詢項目：", font=("Arial", 10, "bold")).pack(pady=5)
        
        self.search_type = StringVar(value="SUPP")
        Radiobutton(window, text="最小支持度計數 (min_supp)", 
                    variable=self.search_type, value="SUPP", command=self.update_label).pack(anchor="w", padx=50)
        Radiobutton(window, text="最小信賴度閾值 (min_con)", 
                    variable=self.search_type, value="CONF", command=self.update_label).pack(anchor="w", padx=50)
        
        # 3. 輸入欄位
        self.input_label = Label(window, text="\n請輸入數值：", font=("Arial", 10))
        self.input_label.pack(pady=5)
        
        self.entry_value = Entry(window, width=20, font=("Arial", 12))
        self.entry_value.pack(pady=5)
        self.entry_value.insert(0, str(self.current_min_supp)) # 填入初始預設值
        
        # 4. 目前狀態顯示
        self.status_label = Label(window, text=f"目前系統參數設定 -> min_supp: {self.current_min_supp} 次 | min_con: {self.current_min_conf*100}%", fg="blue")
        self.status_label.pack(pady=5)
        
        # 5. 執行按鈕
        Button(window, text="開始分析與搜尋", command=self.process_mining, bg="#4CAF50", fg="white", font=("Arial", 11, "bold"), width=15).pack(pady=10)
        
        # 6. 控制結果要顯示什麼
        Label(window, text="結果顯示篩選：", font=("Arial", 10, "bold")).pack(pady=5)
        self.display_mode = StringVar(value="BOTH")
        filter_frame = Frame(window)
        filter_frame.pack(pady=5)
        Radiobutton(filter_frame, text="顯示全部", variable=self.display_mode, value="BOTH", command=self.display_results).pack(side="left", padx=20)
        Radiobutton(filter_frame, text="僅顯示頻繁項集 (min_supp)", variable=self.display_mode, value="SUPP_ONLY", command=self.display_results).pack(side="left", padx=20)
        Radiobutton(filter_frame, text="僅顯示強關聯規則 (min_con)", variable=self.display_mode, value="CONF_ONLY", command=self.display_results).pack(side="left", padx=20)
        
        # 7. 結果顯示區域
        Label(window, text="--- 分析與搜尋結果 ---", font=("Arial", 10, "bold")).pack(anchor="w", padx=20)
        self.result_area = scrolledtext.ScrolledText(window, width=80, height=18, font=("Courier New", 10))
        self.result_area.pack(pady=5, padx=20)

    # 切換想輸入的項目
    def update_label(self):
        if self.search_type.get() == "SUPP":
            self.input_label.config(text="\n請輸入次數 (正整數)：")
            self.entry_value.delete(0, END)
            self.entry_value.insert(0, str(self.current_min_supp))
        else:
            self.input_label.config(text="\n請輸入比例 (0.0 ~ 1.0)：")
            self.entry_value.delete(0, END)
            self.entry_value.insert(0, str(self.current_min_conf))

    # 檢查輸入的數值是否合法
    def process_mining(self):
        val_str = self.entry_value.get().strip()
        
        # 驗證輸入格式
        if self.search_type.get() == "SUPP":
            try:
                val = int(val_str)
                if val <= 0: raise ValueError
                self.current_min_supp = val
            except ValueError:
                messagebox.showerror("輸入錯誤", "min_supp 必須是正整數")
                return
        else:
            try:
                val = float(val_str)
                if not (0.0 <= val <= 1.0): raise ValueError
                self.current_min_conf = val
            except ValueError:
                messagebox.showerror("輸入錯誤", "min_con 必須是 0.0 到 1.0 之間的浮點數")
                return
        # 更新狀態顯示
        self.status_label.config(text=f"目前系統參數設定 -> min_supp: {self.current_min_supp} 次 | min_con: {self.current_min_conf*100}%")
        # 清空結果欄位，寫入新搜尋結果
        dataset, header_table = first_scan(self.file_path, self.current_min_supp)
        if dataset is None:
            messagebox.showerror("錯誤", f"找不到測試檔案 '{self.file_path}'")
            return
        # 建立 FP-Tree，同時更新 header_table 的節點鏈結指標
        build_fp_tree(dataset, header_table)
        self.current_frequent_itemsets = []
        mine_fp_tree(header_table, self.current_min_supp, set([]), self.current_frequent_itemsets)
        self.current_rules = generate_rules(self.current_frequent_itemsets, self.current_min_conf)
        self.display_results()
                
    def display_results(self):
        # 每次切換或重新分析時，先清空文字區域
        self.result_area.delete(1.0, END)
        # 判斷是否要印出min_sup
        if self.display_mode.get() in ["BOTH", "SUPP_ONLY"]:
            self.result_area.insert(END, f"[1. 符合 min_supp >= {self.current_min_supp} 次的頻繁項集]:\n")
            if not self.current_frequent_itemsets:
                self.result_area.insert(END, " (無符合條件之特徵)\n")
            for itemset, support in sorted(self.current_frequent_itemsets, key=lambda x: x[1], reverse=True):
                self.result_area.insert(END, f"  項目組合: {list(itemset)} -> 支持度次數: {support}\n")
        # 判斷是否要印出min_con
        if self.display_mode.get() in ["BOTH", "CONF_ONLY"]:
            self.result_area.insert(END, f"\n[2. 符合 min_con >= {self.current_min_conf*100}% 的強關聯規則]:\n")
            if not self.current_rules:
                self.result_area.insert(END, " (無符合條件之特徵)\n") # 順便幫你補上原本漏掉的右括號 )
            for ant, cons, conf, supp in sorted(self.current_rules, key=lambda x: (x[2], x[3]), reverse=True):
                self.result_area.insert(END, f"  規則: {ant} ---> {cons}\n")
                self.result_area.insert(END, f"        -> 信賴度: {conf*100:.2f}% | 支持度次數: {supp}\n\n")

if __name__ == "__main__":
    root_window = Tk()
    app = FPGrowthGUI(root_window)
    root_window.mainloop()