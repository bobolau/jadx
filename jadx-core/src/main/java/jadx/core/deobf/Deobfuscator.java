package jadx.core.deobf;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import jadx.core.dex.instructions.IndexInsnNode;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.nodes.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import jadx.api.JadxArgs;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.attributes.nodes.SourceFileAttr;
import jadx.core.dex.info.ClassInfo;
import jadx.core.dex.info.FieldInfo;
import jadx.core.dex.info.MethodInfo;
import jadx.core.dex.instructions.args.ArgType;

public class Deobfuscator {
	private static final Logger LOG = LoggerFactory.getLogger(Deobfuscator.class);

	private static final boolean DEBUG = false;

	public static final String CLASS_NAME_SEPARATOR = ".";
	public static final String INNER_CLASS_SEPARATOR = "$";

	private final JadxArgs args;
	@NotNull
	private final List<DexNode> dexNodes;
	private final DeobfPresets deobfPresets;

	private final Map<ClassInfo, DeobfClsInfo> clsMap = new HashMap<>();
	private final Map<FieldInfo, String> fldMap = new HashMap<>();
	private final Map<MethodInfo, String> mthMap = new HashMap<>();

	private final Map<MethodInfo, OverridedMethodsNode> ovrdMap = new HashMap<>();
	private final List<OverridedMethodsNode> ovrd = new ArrayList<>();

	private final PackageNode rootPackage = new PackageNode("");
	private final Set<String> pkgSet = new TreeSet<>();
	private final Set<String> reservedClsNames = new HashSet<>();

	// for load set method only
	private final Set<ClassInfo> setLoadSetGetMethod = new HashSet<>();
	private final Map<FieldInfo, MethodInfo> fieldSetGetMethodMap = new HashMap<>();

	private final int maxLength;
	private final int minLength;
	private final boolean useSourceNameAsAlias;

	private int pkgIndex = 0;
	private int clsIndex = 0;
	private int fldIndex = 0;
	private int mthIndex = 0;

	@Deprecated
	public Deobfuscator(JadxArgs args, @NotNull List<DexNode> dexNodes, File deobfMapFile) {
		this(args, dexNodes, deobfMapFile.toPath());
	}

	public Deobfuscator(JadxArgs args, @NotNull List<DexNode> dexNodes, Path deobfMapFile) {
		this.args = args;
		this.dexNodes = dexNodes;

		this.minLength = args.getDeobfuscationMinLength();
		this.maxLength = args.getDeobfuscationMaxLength();
		this.useSourceNameAsAlias = args.isUseSourceNameAsClassAlias();

		this.deobfPresets = new DeobfPresets(this, deobfMapFile);
	}

	public void execute() {
		// fix, change to always load old
		//if (!args.isDeobfuscationForceSave()) {
			deobfPresets.load();
			initIndexes();
		//}
		process();
		deobfPresets.save(args.isDeobfuscationForceSave());
		clear();
	}

	private void initIndexes() {
		pkgIndex = pkgSet.size();
		clsIndex = deobfPresets.getClsPresetMap().size();
		fldIndex = deobfPresets.getFldPresetMap().size();
		mthIndex = deobfPresets.getMthPresetMap().size();
	}

	private void preProcess() {
		for (DexNode dexNode : dexNodes) {
			for (ClassNode cls : dexNode.getClasses()) {
				Collections.addAll(reservedClsNames, cls.getPackage().split("\\."));
			}
		}
		for (DexNode dexNode : dexNodes) {
			for (ClassNode cls : dexNode.getClasses()) {
				preProcessClass(cls);
			}
		}
	}

	private void process() {
		preProcess();
		if (DEBUG) {
			dumpAlias();
		}
		for (DexNode dexNode : dexNodes) {
			for (ClassNode cls : dexNode.getClasses()) {
				processClass(cls);
			}
		}
		postProcess();
	}

	private void postProcess() {
		int id = 1;
		for (OverridedMethodsNode o : ovrd) {
			boolean aliasFromPreset = false;
			String aliasToUse = null;
			for (MethodInfo mth : o.getMethods()) {
				if (mth.isAliasFromPreset()) {
					aliasToUse = mth.getAlias();
					aliasFromPreset = true;
				}
			}
			for (MethodInfo mth : o.getMethods()) {
				if (aliasToUse == null) {
					if (mth.isRenamed() && !mth.isAliasFromPreset()) {
						mth.setAlias(String.format("mo%d%s", id, prepareNamePart(mth.getName())));
					}
					aliasToUse = mth.getAlias();
				}
				mth.setAlias(aliasToUse);
				mth.setAliasFromPreset(aliasFromPreset);
			}
			id++;
		}
	}

	void clear() {
		deobfPresets.clear();
		clsMap.clear();
		fldMap.clear();
		mthMap.clear();

		ovrd.clear();
		ovrdMap.clear();
	}

	private void resolveOverriding(MethodNode mth) {
		Set<ClassNode> clsParents = new LinkedHashSet<>();
		collectClassHierarchy(mth.getParentClass(), clsParents);

		String mthSignature = mth.getMethodInfo().makeSignature(false);
		Set<MethodInfo> overrideSet = new LinkedHashSet<>();
		for (ClassNode classNode : clsParents) {
			MethodInfo methodInfo = getMthOverride(classNode.getMethods(), mthSignature);
			if (methodInfo != null) {
				overrideSet.add(methodInfo);
			}
		}
		if (overrideSet.isEmpty()) {
			return;
		}
		OverridedMethodsNode overrideNode = getOverrideMethodsNode(overrideSet);
		if (overrideNode == null) {
			overrideNode = new OverridedMethodsNode(overrideSet);
			ovrd.add(overrideNode);
		}
		for (MethodInfo overrideMth : overrideSet) {
			if (!ovrdMap.containsKey(overrideMth)) {
				ovrdMap.put(overrideMth, overrideNode);
				overrideNode.add(overrideMth);
			}
		}
	}

	private OverridedMethodsNode getOverrideMethodsNode(Set<MethodInfo> overrideSet) {
		for (MethodInfo overrideMth : overrideSet) {
			OverridedMethodsNode node = ovrdMap.get(overrideMth);
			if (node != null) {
				return node;
			}
		}
		return null;
	}

	private MethodInfo getMthOverride(List<MethodNode> methods, String mthSignature) {
		for (MethodNode m : methods) {
			MethodInfo mthInfo = m.getMethodInfo();
			if (mthInfo.getShortId().startsWith(mthSignature)) {
				return mthInfo;
			}
		}
		return null;
	}

	private void collectClassHierarchy(ClassNode cls, Set<ClassNode> collected) {
		boolean added = collected.add(cls);
		if (added) {
			ArgType superClass = cls.getSuperClass();
			if (superClass != null) {
				ClassNode superNode = cls.dex().resolveClass(superClass);
				if (superNode != null) {
					collectClassHierarchy(superNode, collected);
				}
			}

			for (ArgType argType : cls.getInterfaces()) {
				ClassNode interfaceNode = cls.dex().resolveClass(argType);
				if (interfaceNode != null) {
					collectClassHierarchy(interfaceNode, collected);
				}
			}
		}
	}

	private void processClass(ClassNode cls) {
		if (isR(cls.getParentClass())) {
			return;
		}
		ClassInfo clsInfo = cls.getClassInfo();
		String fullName = getClassFullName(clsInfo);
		if (!fullName.equals(clsInfo.getFullName())) {
			clsInfo.rename(cls.dex().root(), fullName);
		}

		for (FieldNode field : cls.getFields()) {
			if (field.contains(AFlag.DONT_RENAME)) {
				continue;
			}
			renameField(field);
		}
		for (MethodNode mth : cls.getMethods()) {
			renameMethod(mth);
		}
		for (ClassNode innerCls : cls.getInnerClasses()) {
			processClass(innerCls);
		}
	}

	public void renameField(FieldNode field) {
		FieldInfo fieldInfo = field.getFieldInfo();
		String alias = getFieldAlias(field);
		if (alias != null) {
			fieldInfo.setAlias(alias);
		}
	}

	public void forceRenameField(FieldNode field) {
		field.getFieldInfo().setAlias(makeFieldAlias(field));
	}

	public void renameMethod(MethodNode mth) {
		String alias = getMethodAlias(mth);
		if (alias != null) {
			mth.getMethodInfo().setAlias(alias);
		}
		if (mth.isVirtual()) {
			resolveOverriding(mth);
		}
	}

	public void forceRenameMethod(MethodNode mth) {
		mth.getMethodInfo().setAlias(makeMethodAlias(mth));
		if (mth.isVirtual()) {
			resolveOverriding(mth);
		}
	}

	public void addPackagePreset(String origPkgName, String pkgAlias) {
		PackageNode pkg = getPackageNode(origPkgName, true);
		pkg.setAlias(pkgAlias);
	}

	/**
	 * Gets package node for full package name
	 *
	 * @param fullPkgName full package name
	 * @param create      if {@code true} then will create all absent objects
	 * @return package node object or {@code null} if no package found and <b>create</b> set to {@code false}
	 */
	private PackageNode getPackageNode(String fullPkgName, boolean create) {
		if (fullPkgName.isEmpty() || fullPkgName.equals(CLASS_NAME_SEPARATOR)) {
			return rootPackage;
		}
		PackageNode result = rootPackage;
		PackageNode parentNode;
		do {
			String pkgName;
			int idx = fullPkgName.indexOf(CLASS_NAME_SEPARATOR);

			if (idx > -1) {
				pkgName = fullPkgName.substring(0, idx);
				fullPkgName = fullPkgName.substring(idx + 1);
			} else {
				pkgName = fullPkgName;
				fullPkgName = "";
			}
			parentNode = result;
			result = result.getInnerPackageByName(pkgName);
			if (result == null && create) {
				result = new PackageNode(pkgName);
				parentNode.addInnerPackage(result);
			}
		} while (!fullPkgName.isEmpty() && result != null);

		return result;
	}

	String getNameWithoutPackage(ClassInfo clsInfo) {
		String prefix;
		ClassInfo parentClsInfo = clsInfo.getParentClass();
		if (parentClsInfo != null) {
			DeobfClsInfo parentDeobfClsInfo = clsMap.get(parentClsInfo);
			if (parentDeobfClsInfo != null) {
				prefix = parentDeobfClsInfo.makeNameWithoutPkg();
			} else {
				prefix = getNameWithoutPackage(parentClsInfo);
			}
			prefix += INNER_CLASS_SEPARATOR;
		} else {
			prefix = "";
		}
		return prefix + clsInfo.getShortName();
	}

	private void preProcessClass(ClassNode cls) {
		ClassInfo classInfo = cls.getClassInfo();
		String pkgFullName = classInfo.getPackage();
		PackageNode pkg = getPackageNode(pkgFullName, true);
		doPkg(pkg, pkgFullName);

		String alias = deobfPresets.getForCls(classInfo);
		if (alias != null) {
			clsMap.put(classInfo, new DeobfClsInfo(this, cls, pkg, alias));
		} else {
			if (!clsMap.containsKey(classInfo)) {
				String clsShortName = classInfo.getShortName();
				if (shouldRename(clsShortName) || reservedClsNames.contains(clsShortName)) {
					makeClsAlias(cls);
				}
			}
		}
		for (ClassNode innerCls : cls.getInnerClasses()) {
			preProcessClass(innerCls);
		}
	}

	public String getClsAlias(ClassNode cls) {
		DeobfClsInfo deobfClsInfo = clsMap.get(cls.getClassInfo());
		if (deobfClsInfo != null) {
			return deobfClsInfo.getAlias();
		}
		return makeClsAlias(cls);
	}

	private String makeClsAlias(ClassNode cls) {
		ClassInfo classInfo = cls.getClassInfo();
		String alias = null;

		if (this.useSourceNameAsAlias) {
			alias = getAliasFromSourceFile(cls);
		}

		if (alias == null) {
			String clsName = classInfo.getShortName();
			alias = String.format("C%04d%s", clsIndex++, prepareNamePart(clsName));
		}
		PackageNode pkg = getPackageNode(classInfo.getPackage(), true);
		clsMap.put(classInfo, new DeobfClsInfo(this, cls, pkg, alias));
		return alias;
	}

	@Nullable
	private String getAliasFromSourceFile(ClassNode cls) {
		SourceFileAttr sourceFileAttr = cls.get(AType.SOURCE_FILE);
		if (sourceFileAttr == null) {
			return null;
		}
		if (cls.getClassInfo().isInner()) {
			return null;
		}
		String name = sourceFileAttr.getFileName();
		if (name.endsWith(".java")) {
			name = name.substring(0, name.length() - ".java".length());
		} else if (name.endsWith(".kt")) {
			name = name.substring(0, name.length() - ".kt".length());
		}
		if (!NameMapper.isValidIdentifier(name) || NameMapper.isReserved(name)) {
			return null;
		}
		for (DeobfClsInfo deobfClsInfo : clsMap.values()) {
			if (deobfClsInfo.getAlias().equals(name)) {
				return null;
			}
		}
		ClassNode otherCls = cls.dex().root().searchClassByName(cls.getPackage() + '.' + name);
		if (otherCls != null) {
			return null;
		}
		cls.remove(AType.SOURCE_FILE);
		return name;
	}

	@Nullable
	private String getFieldAlias(FieldNode field) {
		FieldInfo fieldInfo = field.getFieldInfo();
		String alias = fldMap.get(fieldInfo);
		if (alias != null) {
			return alias;
		}
		alias = deobfPresets.getForFld(fieldInfo);
		if (alias != null) {
			fldMap.put(fieldInfo, alias);
			return alias;
		}
		if (shouldRename(field.getName())) {
			return makeFieldAlias(field);
		}
		return null;
	}

	@Nullable
	private String getMethodAlias(MethodNode mth) {
		MethodInfo methodInfo = mth.getMethodInfo();
		if (methodInfo.isClassInit() || methodInfo.isConstructor()) {
			return null;
		}
		String alias = mthMap.get(methodInfo);
		if (alias != null) {
			return alias;
		}
		alias = deobfPresets.getForMth(methodInfo);
		if (alias != null) {
			mthMap.put(methodInfo, alias);
			methodInfo.setAliasFromPreset(true);
			return alias;
		}
		if (shouldRename(mth.getName())) {
			return makeMethodAlias(mth);
		}
		return null;
	}

	public String makeFieldAlias(FieldNode field) {
		// 1. try to get field name via set method name
		String alias = getAliasBySetGetMethod(field.getParentClass(), field);

		// 2. try to get field name by field type
		if(alias==null ){
			alias = getAliasByFieldType(field);
		}
		if(alias==null){
			alias = String.format("f%d%s", fldIndex++, prepareNamePart(field.getName()));
		}
		fldMap.put(field.getFieldInfo(), alias);
		return alias;
	}

	private String getAliasByFieldType(FieldNode field){
		// 检查字段类型，如果不为String和Array/List/Set集合类，则检查该类型的字段数量，数量为1则直接用类型来命名字段
		String alias = null;
		// final or static field,  String
		if((field.getAccessFlags().isFinal() || field.getAccessFlags().isStatic() ) && field.getType().isObject()){
			if("java.lang.String".equals(field.getType().getObject())
					&& field.getAttributesStringsList().size()>0
					&& field.getAttributesStringsList().get(0).indexOf("V=")>=0
			){
				//V=xxx
				alias = field.getAttributesStringsList().get(0).substring(2);//.toUpperCase();
				if(alias.length()<=2){
					alias = "fld_" + alias;
				}
				return alias;
			}
		}
		if(!field.getType().isPrimitive() && field.getType().isObject()
				&& !"java.lang.String".equals(field.getType().getObject())){
			String type = field.getType().getObject();
			int startIndex = type.lastIndexOf(".")+1;
			// when start with "I", then next char. such as IItemObject (ascii I=73)
			if(type.charAt(startIndex)==73){
				startIndex += 1;
			}
			alias = new StringBuilder().append(Character.toLowerCase(type.charAt(startIndex))).append(type.substring(startIndex+1)).toString();

		}
		return alias;
	}

	private String getAliasBySetGetMethod(ClassNode cls, FieldNode field){
		String alias = null;
		if(!setLoadSetGetMethod.contains(cls.getClassInfo())){
			for (MethodNode mth : cls.getMethods()) {
				try {
					// ignore non get/set method
					if(!mth.getName().startsWith("set") && !mth.getName().startsWith("get") ){
						continue;
					}
					// load set method
					mth.load();
					// check mapping field
					InsnNode[] insnNodes = mth.getInstructions();
					if(insnNodes!=null){
						for(int i=0; i<insnNodes.length && i<3; i++){
							if(insnNodes[i]==null
									|| !(insnNodes[i] instanceof IndexInsnNode)
									|| !(((IndexInsnNode)insnNodes[i]).getIndex() instanceof FieldInfo)){
								continue;
							}
							Object indexObject = ((IndexInsnNode)insnNodes[i]).getIndex();
							// set method
							if(mth.getName().startsWith("set")
									&& InsnType.IPUT.equals(insnNodes[i].getType())){
								fieldSetGetMethodMap.put((FieldInfo)indexObject, mth.getMethodInfo());
								break;

							}
							// get method
							if(mth.getName().startsWith("get")
									&& mth.getReturnType().isObject()
									&& ((FieldInfo)indexObject).getType().getObject().equals(mth.getReturnType().getObject())){
								if(fieldSetGetMethodMap.containsKey((FieldInfo)indexObject)){
									break;
								}
								fieldSetGetMethodMap.put((FieldInfo)indexObject, mth.getMethodInfo());
								LOG.warn(mth.getMethodInfo()+" => " + (FieldInfo)indexObject);
								break;
							}
						}
					}
				} catch (Exception e) {
					mth.addError("Method load error", e);
				}
			}
			setLoadSetGetMethod.add(cls.getClassInfo());
		}

		if(fieldSetGetMethodMap.containsKey(field.getFieldInfo())){
			MethodInfo method = fieldSetGetMethodMap.get(field.getFieldInfo());
			if(!method.isRenamed()){
				// setFieldName/getFieldName
				alias = new StringBuilder().append(Character.toLowerCase(method.getName().charAt(3))).append(method.getName().substring(4)).toString();
			}
		}
		return alias;
	}


	public String makeMethodAlias(MethodNode mth) {
		String alias = String.format("m%d%s", mthIndex++, prepareNamePart(mth.getName()));
		mthMap.put(mth.getMethodInfo(), alias);
		return alias;
	}

	private void doPkg(PackageNode pkg, String fullName) {
		if (pkgSet.contains(fullName)) {
			return;
		}
		pkgSet.add(fullName);

		// doPkg for all parent packages except root that not hasAliases
		PackageNode parentPkg = pkg.getParentPackage();
		while (!parentPkg.getName().isEmpty()) {
			if (!parentPkg.hasAlias()) {
				doPkg(parentPkg, parentPkg.getFullName());
			}
			parentPkg = parentPkg.getParentPackage();
		}

		String pkgName = pkg.getName();
		if (!pkg.hasAlias() && shouldRename(pkgName)) {
			String pkgAlias = String.format("p%03d%s", pkgIndex++, prepareNamePart(pkgName));
			pkg.setAlias(pkgAlias);
		}
	}

	private boolean shouldRename(String s) {
		if("id".equals(s)){
			return false;
		}
		int len = s.length();
		return len < minLength || len > maxLength
				|| !NameMapper.isValidIdentifier(s);
	}

	private String prepareNamePart(String name) {
		if (name.length() > maxLength) {
			return 'x' + Integer.toHexString(name.hashCode());
		}
		return NameMapper.removeInvalidCharsMiddle(name);
	}

	private void dumpClassAlias(ClassNode cls) {
		PackageNode pkg = getPackageNode(cls.getPackage(), false);

		if (pkg != null) {
			if (!cls.getFullName().equals(getClassFullName(cls))) {
				LOG.info("Alias name for class '{}' is '{}'", cls.getFullName(), getClassFullName(cls));
			}
		} else {
			LOG.error("Can't find package node for '{}'", cls.getPackage());
		}
	}

	private void dumpAlias() {
		for (DexNode dexNode : dexNodes) {
			for (ClassNode cls : dexNode.getClasses()) {
				dumpClassAlias(cls);
			}
		}
	}

	private String getPackageName(String packageName) {
		PackageNode pkg = getPackageNode(packageName, false);
		if (pkg != null) {
			return pkg.getFullAlias();
		}
		return packageName;
	}

	private String getClassName(ClassInfo clsInfo) {
		DeobfClsInfo deobfClsInfo = clsMap.get(clsInfo);
		if (deobfClsInfo != null) {
			return deobfClsInfo.makeNameWithoutPkg();
		}
		return getNameWithoutPackage(clsInfo);
	}

	private String getClassFullName(ClassNode cls) {
		return getClassFullName(cls.getClassInfo());
	}

	private String getClassFullName(ClassInfo clsInfo) {
		DeobfClsInfo deobfClsInfo = clsMap.get(clsInfo);
		if (deobfClsInfo != null) {
			return deobfClsInfo.getFullName();
		}
		return getPackageName(clsInfo.getPackage()) + CLASS_NAME_SEPARATOR + getClassName(clsInfo);
	}

	public Map<ClassInfo, DeobfClsInfo> getClsMap() {
		return clsMap;
	}

	public Map<FieldInfo, String> getFldMap() {
		return fldMap;
	}

	public Map<MethodInfo, String> getMthMap() {
		return mthMap;
	}

	public PackageNode getRootPackage() {
		return rootPackage;
	}

	private static boolean isR(ClassNode cls) {
		if (!cls.getClassInfo().getShortName().equals("R")) {
			return false;
		}
		if (!cls.getMethods().isEmpty() || !cls.getFields().isEmpty()) {
			return false;
		}
		for (ClassNode inner : cls.getInnerClasses()) {
			for (MethodNode m : inner.getMethods()) {
				if (!m.getMethodInfo().isConstructor() && !m.getMethodInfo().isClassInit()) {
					return false;
				}
			}
			for (FieldNode field : cls.getFields()) {
				ArgType type = field.getType();
				if (type != ArgType.INT && (!type.isArray() || type.getArrayElement() != ArgType.INT)) {
					return false;
				}
			}
		}
		return true;
	}
}
