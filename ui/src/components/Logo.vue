<script setup lang="ts">
import { boot } from '../core/boot';
</script>
<template><img v-if="boot.logo" :src="boot.logo" alt="" width="28" height="28" class="sp-logo"></template>
<style scoped>.sp-logo { width: 28px; height: 28px; flex: none; }</style>
