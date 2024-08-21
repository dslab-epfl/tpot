CURDIR=`pwd`
ORIG_DIR=../.tmp/usbmouse_original

# Suppress output
pushd () {
    command pushd "$@" > /dev/null
}
popd () {
    command popd "$@" > /dev/null
}

rm -rf $ORIG_DIR
mkdir -p $ORIG_DIR

pushd $ORIG_DIR
# Download the Verifast case study
wget -q https://github.com/verifast/verifast/archive/refs/heads/master.zip
unzip -q master.zip

mkdir relevant_components
cp verifast-master/examples/usbkbd/src/usbmouse_original.c \
    verifast-master/examples/usbkbd/src/equals.h\
    relevant_components
cp verifast-master/examples/usbkbd/src/usbmouse.c relevant_components/usbmouse_verifast.c
cp  relevant_components/usbmouse_verifast.c
cp -r verifast-master/examples/usbkbd/src/linux relevant_components/

# Need to remove some lines to avoid nested block comments. Otherwise the source will not compile.
sed -i '48s/.*//' relevant_components/linux/mod_devicetable.h # /*
sed -i '60s/.*//' relevant_components/linux/mod_devicetable.h # */

sed -i '257s/ep0.*//' relevant_components/linux/usb.h # /* */
sed -i '500s/.*//' relevant_components/linux/usb.h # /*
sed -i '505s/.*//' relevant_components/linux/usb.h # */
sed -i '511s/.*//' relevant_components/linux/usb.h # /* */
sed -i '533s/.*//' relevant_components/linux/usb.h # /*
sed -i '545s/.*//' relevant_components/linux/usb.h # */
sed -i '878s/setup_packet.*//' relevant_components/linux/usb.h # /* */

sed -i '174s/.*//' relevant_components/linux/input.h # /*
sed -i '180s/.*//' relevant_components/linux/input.h # */

# usbmouse_tpot.c is the same as usbmouse_verifast.c, but without the VeriFast annotations
perl -0777 -p -e 's/\/\*@.*?@\*\///sg' relevant_components/usbmouse_verifast.c > relevant_components/usbmouse_tpot.c
# Remove VeriFast annotations ( //@ ... )
perl -0777 -pi -e 's/\/\/@.*//g' relevant_components/usbmouse_tpot.c
# perl -0777 -pi -e 's/\/\/@\s.*//' relevant_components/usbmouse_tpot.c



# # # Copy the version verified by TPOT, leaving out TPOT-specific files and scripts
mkdir tpot_target
cp -r $CURDIR/usbmouse_tpot.c \
      $CURDIR/usbmouse_verifast.c \
      $CURDIR/usbmouse_original.c \
      $CURDIR/equals.h \
      $CURDIR/linux \
      tpot_target

# Remove the markers used to count lines of specs.
perl -pi -e 's/\/\*SPEC\*\/ //g' tpot_target/usbmouse_verifast.c
perl -pi -e 's/\/\*PREDICATE\*\///g' tpot_target/usbmouse_verifast.c
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/usbmouse_verifast.c
perl -pi -e 's/\/\*PROOF\*\///g' tpot_target/usbmouse_verifast.c

perl -pi -e 's/\/\/INTERNAL\/\/ //g' tpot_target/linux/input.h
perl -pi -e 's/\/\*INTERNAL\*\/ //g' tpot_target/linux/input.h
perl -pi -e 's/\/\/SYNTAX\/\///g' tpot_target/linux/input.h
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/linux/input.h

perl -pi -e 's/\/\/INTERNAL\/\/ //g' tpot_target/linux/mod_devicetable.h
perl -pi -e 's/\/\*INTERNAL\*\/ //g' tpot_target/linux/mod_devicetable.h
perl -pi -e 's/\/\/SYNTAX\/\///g' tpot_target/linux/mod_devicetable.h
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/linux/mod_devicetable.h

perl -pi -e 's/\/\/INTERNAL\/\/ //g' tpot_target/linux/usb.h
perl -pi -e 's/\/\*INTERNAL\*\/ //g' tpot_target/linux/usb.h
perl -pi -e 's/\/\/SYNTAX\/\///g' tpot_target/linux/usb.h
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/linux/usb.h

perl -pi -e 's/\/\/INTERNAL\/\/ //g' tpot_target/linux/slab_def.h
perl -pi -e 's/\/\*INTERNAL\*\/ //g' tpot_target/linux/slab_def.h
perl -pi -e 's/\/\/SYNTAX\/\///g' tpot_target/linux/slab_def.h
perl -pi -e 's/\/\*SYNTAX\*\///g' tpot_target/linux/slab_def.h
# # Diff the two directories
diff -r relevant_components tpot_target

popd 